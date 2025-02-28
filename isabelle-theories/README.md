## How to Use the Isabelle Theories

To prepare building the session follow these steps:
1. Install Isabelle: [https://isabelle.in.tum.de/](https://isabelle.in.tum.de/).
2. Download the archive of formal proofs (AFP): [https://www.isa-afp.org/download/](https://www.isa-afp.org/download/)
3. Make the whole AFP available to Isabelle (see [https://www.isa-afp.org/help/](https://www.isa-afp.org/help/))


Then, build the session:
- In the repository where the theories are stored execute the following:
   ```bash
   isabelle build -o document=pdf -o document_variants=document:outline=/proof,/ML -P out -d . EnergyGames

- See the resulting files in /out, the outline will be in /out/AFP/EnergyGames 