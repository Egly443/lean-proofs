import sys
import subprocess
import json
import socket
import os
import argparse
import time
import select
from pathlib import Path

# --- CONFIGURATION ---
REPL_CMD = ["stdbuf", "-oL", "lake", "exe", "repl"]
SOCKET_FILE = Path(".lean_bridge.sock")

class LeanBridgeServer:
    def __init__(self):
        self.proc = None
        self.sock = None
        self.state_id = None

    def _read_lean_output(self):
        """Accumulates lines until a valid JSON object is formed."""
        buffer = ""
        while True:
            line = self.proc.stdout.readline()
            if not line: return None
            if not buffer and not line.strip(): continue
            buffer += line
            try:
                json.loads(buffer)
                return buffer
            except json.JSONDecodeError:
                continue

    def start(self, lean_file):
        print(f"[*] Starting Lean REPL for {lean_file}...")
        try:
            self.proc = subprocess.Popen(
                REPL_CMD,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=sys.stderr,
                text=True,
                bufsize=1
            )
        except Exception as e:
            print(f"Error starting process: {e}")
            sys.exit(1)

        # --- KEY FIX: LOAD THE ENTIRE FILE, NOT JUST IMPORTS ---
        try:
            with open(lean_file, 'r') as f:
                content = f.read()
            
            print(f"[*] Sending {len(content)} bytes of Lean code to REPL...")
            
            # Send the whole file as one command. This defines namespaces, 
            # variables, and types in the REPL environment.
            payload = {"cmd": content}
            self.proc.stdin.write(json.dumps(payload) + "\n\n")
            self.proc.stdin.flush()
            
            print("[*] Waiting for Lean response (may take 60s+ for Mathlib)...")
            r, _, _ = select.select([self.proc.stdout], [], [], 120)
            
            if r:
                response_line = self._read_lean_output()
            else:
                print("Timeout waiting for Lean response.")
                self.proc.terminate()
                sys.exit(1)
                
            if not response_line:
                print(f"Error: Lean process died.")
                sys.exit(1)
                
            res = json.loads(response_line.strip())
            
            # Check for actual errors (ignore warnings)
            if "messages" in res:
                errors = [m for m in res["messages"] if m.get("severity") == "error"]
                if errors:
                    print("[!] CRITICAL ERRORS in file loading:")
                    for e in errors: print(f"  Line {e['pos']['line']}: {e['data']}")
                    # We don't exit here because sometimes minor errors are recoverable
            
            # Capture the environment ID
            self.state_id = res.get("env", 0)
            print(f"[*] Environment loaded. Base State ID: {self.state_id}")
            
        except Exception as e:
            print(f"Error during initialization: {e}")
            if self.proc: self.proc.terminate()
            sys.exit(1)

        if SOCKET_FILE.exists(): SOCKET_FILE.unlink()
        self.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.sock.bind(str(SOCKET_FILE))
        self.sock.listen(1)
        print(f"[*] Server ready. Listening on {SOCKET_FILE}")
        self._loop()

    def _loop(self):
        while True:
            conn, _ = self.sock.accept()
            with conn:
                try:
                    data = conn.recv(65536).decode() # Increased buffer size
                    if not data: continue
                    req = json.loads(data)
                    reply = {"status": "error", "message": "Invalid request"}

                    if req.get("command") == "tactic":
                        payload = {"tactic": req["tactic"], "proofState": req.get("proof_state", self.state_id)}
                        self.proc.stdin.write(json.dumps(payload) + "\n\n")
                        self.proc.stdin.flush()
                        resp = self._read_lean_output()
                        if resp:
                            lean_res = json.loads(resp)
                            if "goals" in lean_res:
                                reply = {"status": "success", "goals": lean_res["goals"], "new_state_id": lean_res.get("proofState")}
                            else:
                                reply = {"status": "error", "message": str(lean_res.get("messages", "Unknown error"))}
                    
                    elif req.get("command") == "cmd":
                        payload = {"cmd": req["cmd"], "env": self.state_id} # Pass env to keep context
                        self.proc.stdin.write(json.dumps(payload) + "\n\n")
                        self.proc.stdin.flush()
                        resp = self._read_lean_output()
                        if resp:
                            lean_res = json.loads(resp)
                            reply = {"status": "success", "response": lean_res}

                    conn.sendall(json.dumps(reply).encode())
                except Exception as e:
                    pass

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="mode")
    srv = subparsers.add_parser("server")
    srv.add_argument("file")
    args = parser.parse_args()
    if args.mode == "server":
        LeanBridgeServer().start(args.file)
