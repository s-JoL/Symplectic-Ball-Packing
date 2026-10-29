import verification.Statement
import verification.Computability
import verification.EpochComputability
import verification.Audit.Collar
import verification.Audit.Compile
import verification.Audit.Consequences
import verification.Audit.Effective
import verification.Audit.GlobalFlow
import verification.Audit.PackingCertificate
import verification.Audit.PackingCertificateJoint
import verification.Audit.PackingCertificatePolynomial
import verification.Audit.RawFullProduct
import verification.Audit.RawMoser
import verification.Audit.Branches
import verification.Audit.SqrtName
import verification.Audit.Independence
import verification.Audit.VendoredUsage

/-!
# Audits

Imports every audit module except the generated `PaperTags.lean`. Each audit module checks one
group of intermediate results and definitions of the construction by
`#assert_publication_axioms`, `#check_explicit` and sample `#eval`s; `Independence.lean` and
`VendoredUsage.lean` check the dependency closure of the main theorems. The library target
`verification` builds every module under `verification/`, so each audit module is checked
whether or not it is imported here.
-/
