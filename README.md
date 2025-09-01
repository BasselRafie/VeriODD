# VeriODD

**VeriODD** is an ANTLR-based toolchain that compiles YAML ODD/COD specifications into  
(i) human-readable *propositional logic formulas* and (ii) solver-ready *SMT-LIB* for automated verification with **Z3**.  
It supports module-level checks (consistency and COD-in-ODD) and comes with a simple GUI.

---

## Quick start

### Prerequisites
- **Java JDK 24+**
- **Maven**

### Run
Clone this repository, navigate to JAR -> VeriODD.jar and start the tool.

OR

Clone this repository, build it as a maven project, navigate to src -> main -> java -> veriodd and run `VeriODD.java`.



**Example ODD:**
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
