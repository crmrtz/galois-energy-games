With this theory we provide a formal proof of decidability of Bisping's declining energy games. 

To build the session follow these steps:
- Download the archive of formal proofs (AFP) from https://www.isa-afp.org/download/
- Make the whole AFP available to Isabelle (see https://www.isa-afp.org/help/)
- In the repository where the theories are stored execute the following:
    - isabelle build -o document=pdf -o document_variants=document:outline=/proof,/ML -P out -d . EnergyGames
- See the resulting files in /out, the outline will be in /out/AFP/EnergyGames 