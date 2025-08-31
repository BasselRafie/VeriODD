# VeriODD

**VeriODD** is an ANTLR-based toolchain that compiles YAML ODD/COD specifications into  
(i) human-readable *propositional logic formulas* and (ii) solver-ready *SMT-LIB* for automated verification with **Z3**.  
It supports module-level checks (consistency and COD-in-ODD) and comes with a simple GUI.

---

## Features

- **Direct translation from YAML**
  - ODD → Propositional Logic, SMT-LIB
  - COD → Propositional Logic, SMT-LIB
- **Module-level reasoning**
  - Assert one or more ODD modules
  - Optionally include COD facts
- **Integrated verification**
  - One-click `(check-sat)` and optional `(get-model)`; results shown in the UI
  - “Show Combined SMT-LIB” preview
- **Deterministic, auditable pipeline**
  - ANTLR4 grammars: `ODD.g4`, `COD.g4`
  - Visitors: `ODDVisitorSMTLIB`, `ODDVisitorPropositionalLogic`, `CODVisitorSMTLIB`, `CODVisitorPropositionalLogic`
- **Tested**
  - 145 golden unit tests across all four translators


**Example ODD (excerpt):**
```yaml
supported_parking_lot_conditions:
    INCLUDE_AND:
        parking_lot_length: > 12 m
        is_curve: true

unsupported_parking_lot_conditions:
    INCLUDE_AND:
        surface:
            - puddle
            - snow_covered
        location:
            - on_shoulder
            - partly_on_subject_vehicle_lane

parking_lot_conditions:
    INCLUDE_AND:
        - supported_parking_lot_conditions
    EXCLUDE_OR:
        - unsupported_parking_lot_conditions
```

**Example COD:**
```yaml
parking_lot_length: = 13
is_curve: true
surface: snow_covered
location: on_shoulder
```

---

## Quick start

### Prerequisites
- **Java 11+**
- **Maven** or **Gradle**
- **Z3** with Java bindings (jar + native library on your `java.library.path`)

### Run
Clone this repository, build it, and run the `VeriODD` class:

- Start screen: choose **Translate** or **Verify**.
- **Translate mode:** pick input type (ODD/COD) and target (Propositional / SMT-LIB).
- **Verify mode:** paste ODD and COD; select ODD module(s); choose `check-sat` and/or `get-model`; press **Verify**.  
  Use **Show Combined SMT-LIB** to inspect the exact script sent to Z3.

---


## Testing
Run all unit tests (golden output checks for all translators):
```bash
mvn -q test
```

---

## Performance evaluation (optional)
A small harness is included (e.g., `Evaluation.java`) to measure end-to-end validation time across batches of CODs and different ODD sizes (build + run with your preferred parameters). Results show approximately linear scaling with the number of CODs.

---

## Troubleshooting
- **Z3 native library not found**  
  Ensure the Z3 native lib is on `java.library.path` (e.g., `-Djava.library.path=/path/to/z3/bin`) and the Z3 jar is on the classpath.
- **Model differs from expectation**  
  A model is returned only on `SAT` and only if `(get-model)` is requested.

---

## Roadmap
- Align grammars with the **latest ASAM OpenODD** schema (minor gaps remain).
- **Public API** for embedding VeriODD in external tools/services.
- Optional **CVC5** backend in addition to Z3.

---

## Cite
If you use VeriODD in academic work, please cite:
```
VeriODD: A Tool for Translating YAML ODD/COD to Propositional Logic and SMT-LIB for Solver-Based Verification
```
*(BibTeX to be provided upon publication.)*

---

## License
MIT (proposed). See `LICENSE`.

---

## Acknowledgments
We thank our industry collaborators for sharing internal ODD/COD materials that informed the input taxonomy, and acknowledge the conceptual method of Aniculaesei et al. (2023), which VeriODD automates end-to-end.
