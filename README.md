# searching-for-consensus
Using Alloy to find a (3,2)-set-consensus object

We use the Alloy model-finder to find a deterministic object that solves (3,2)-set-consensus and does not solve consensus for 2 processors (in the wait-free model).
We find such an object with 8 states but no less. It makes sense that 8 states is the minimum because each processor must at least write one bit to indicate that it is participating.

Related work: An object equivalent to (3,2)-set-consensus, found without solver assistance, was presented in the paper "Deterministic Objects Give Life to Non-Deterministic 1-Consensus Tasks" at DISC 2018.
