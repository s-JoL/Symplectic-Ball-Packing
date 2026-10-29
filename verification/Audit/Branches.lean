import SymplecticPacking.General.Main
import verification.AxiomCheck

/-!
# The case embeddings

Axiom gates and explicitness checks for the embedding datum of each case of the construction
(`General.selectEmbeddings`) and for its correctness theorems.
-/

#assert_publication_axioms SymplecticPacking.Branch2.embeddings_spec
#assert_publication_axioms SymplecticPacking.Branch2.embeddingsEq_spec
#assert_publication_axioms SymplecticPacking.Branch2.embeddingsGen_spec
#assert_publication_axioms SymplecticPacking.BranchSmall.embeddings_spec
#assert_publication_axioms SymplecticPacking.BranchLargeHigh.embeddings_spec
#assert_publication_axioms SymplecticPacking.BranchLarge3.embeddings_spec
#assert_publication_axioms SymplecticPacking.General.selectEmbeddings_spec
#assert_publication_axioms SymplecticPacking.General.packing_main

#check_explicit SymplecticPacking.Branch2.embeddings
#check_explicit SymplecticPacking.BranchSmall.embeddings
#check_explicit SymplecticPacking.BranchLargeHigh.embeddings
#check_explicit SymplecticPacking.BranchLarge3.embeddings
#check_explicit SymplecticPacking.General.selectEmbeddings
