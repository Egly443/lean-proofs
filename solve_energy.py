from agent import ProofSearch

# We explicitly open the namespace and redeclare the variables (V, Fintype, etc.)
# because the agent runs outside the scope of the original file's "variable" declaration.
THEOREM_INCREMENT = """
open EnergyIncrement
open Finset BigOperators

theorem energy_increment_step {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Finset (Finset V)) (A B : Finset V) 
    (hA : A ∈ parts) (hB : B ∈ parts)
    (ε : ℝ) (hε : 0 < ε) (hirr : IsIrregular G ε A B) :
    ∃ parts' : Finset (Finset V),
      energy G parts' ≥ energy G parts + 
        ε^4 * (A.card * B.card : ℝ) / (Fintype.card V : ℝ)^2 := by sorry
"""

agent = ProofSearch(THEOREM_INCREMENT)

# We prioritize the specific tactics needed for this proof
agent.tactics = [
    # 1. Break down the irregularity witness (The "hirr" hypothesis)
    "obtain ⟨X, hXA, Y, hYB, hXsize, hYsize, hdev⟩ := hirr",
    
    # 2. Construct the new partition using the witness sets
    "use refinePartition parts A B X Y",
    
    # 3. Apply the core lemma (variance_lower_bound) which we already proved
    #    Note: We map the arguments from the context to the lemma
    "apply variance_lower_bound G (le_of_lt hε) hXsize hYsize hdev",
    
    # 4. Handle any remaining arithmetic inequalities
    "linarith",
    "gcongr"
]

agent.run()
