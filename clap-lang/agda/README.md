## Contents

* `CLAP-BASE.agda` basic definitions
   - `Circuit` circuit datatype parameterized by `Gate` datatype
   - `genTrace` witness (i.e.,trace) generator
   - `genCS` constraint-system generator
   - `satCS` satifiability checker (checks whether trace satisfies a constraint-system)

* `CLAP-PROPERTIES.agda`
  - `completenessSeq` proof that complete circuits sequentially compose into complete circuits
  - `soundnessSeq` proof that sound circuits sequentially compose into sound circuits 
  - we skip parallel composition but note that the proof is exactly the same as for sequential composition

* `CLAP-INSTANCE.agda` 
   - instantiation of basic definitions with couple of basic gates (`add`, `eq0`, `const`, etc.)
   - proofs of properties neccessary to instantiate results from compositionality results `CLAP-PROPERTIES.agda`

* `CLAP-MONAD.agda` state monad which provides combinators for circuit composition

* `CLAP-EXAMPLES.agda` couple of simple circuits
   



