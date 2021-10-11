# convEuc
A translator that converts geometric proofs in the Euc language into Isabelle/HOL.\
(See http://www.michaelbeeson.com/research/FoundationsOfGeometry/index.php?include=CheckingEuclid)

Written in C++.

# Requirements
  * `g++` with `c++17` or later;
  * `GNU Make`;
  * (Optional) `Isabelle` (for verification).

# Installation
Building from source:
```
git clone https://github.com/hulsemohit/convEuc.git
cd convEuc
make
```

# Generate Proofs
The following command runs the translator on the _.prf_ files listed in _list.txt_. These  are found in the _eucfiles_ directory.
```
make generate
```
The proofs are written as _.thy_ files in the _thyfiles_ directory.

# Verification
Isabelle can verify the correctness of the generated proofs using the command below. This may take a couple of minutes.
```
isabelle -d thyfiles -v Euc
```
Note that Isabelle needs to be installed and _ROOT_ must be present in _thyfiles_.
