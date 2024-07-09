## Contents

* `CLAP-BASE.agda` basic definitions
   - `Circuit` circuit datatype parameterized by `Gate` datatype
   - `genTrace` trace generator
   - `genCS` constraint-system generator
   - `satCS` satifiability checker

* `CLAP-PROPERTIES.agda`
  - `completeness-composable` proof that complete circuits sequentially compose into complete circuits
  - `soundness-composable` proof that sound circuits sequentially compose into sound circuits 
  - we skip parallel composition but note that the proof is exactly the same as for sequential composition

* `CLAP-INSTANCE.agda` 
   - instantiation of basic definitions with couple of basic gates (`add`, `eq0`, `const`, etc.)
   - proofs of properties neccessary to instantiate results from compositionality results `CLAP-PROPERTIES.agda`

* `CLAP-MONAD.agda` state monad for circuit composition

* `CLAP-EXAMPLES.agda` couple of simple circuits
   



