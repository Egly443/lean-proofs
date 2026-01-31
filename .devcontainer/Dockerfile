# Proof-to-Publication Orchestrator Development Container
FROM ubuntu:22.04

# Avoid prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    build-essential \
    python3.11 \
    python3.11-venv \
    python3-pip \
    texlive-base \
    texlive-latex-extra \
    texlive-fonts-recommended \
    && rm -rf /var/lib/apt/lists/*

# Make python3.11 the default
RUN update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.11 1 && \
    update-alternatives --install /usr/bin/python python /usr/bin/python3.11 1

# Install elan (Lean version manager)
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.8.0

# Add elan to PATH
ENV PATH="/root/.elan/bin:${PATH}"

# Create workspace directory
WORKDIR /workspaces/lemma

# Copy requirements first for caching
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy the rest of the project
COPY . .

# Download Mathlib cache (will be run on container start if needed)
# This is done in postCreateCommand to ensure lake-manifest.json is present

# Expose the orchestrator port
EXPOSE 8000

# Default command
CMD ["python", "-m", "orchestrator.server"]
