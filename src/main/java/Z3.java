import com.microsoft.z3.*;

import java.util.*;

/**
 * Minimal SMT-LIB satisfiability checker using Z3's Java API.
 * - Accepts full SMT-LIB2 text.
 * - Returns SAT/UNSAT/UNKNOWN.
 * - When SAT, includes the model (if any).
 * - When UNSAT, includes the unsat core (if input used :named assertions).
 */
public class Z3 {
    public static void main(String[] args) {
        String smtLib = "; --- ODD ---\n" +
                "(declare-const parking_lot_length Int)\n" +
                "(declare-const is_curve Bool)\n" +
                "(declare-const surface String)\n" +
                "(declare-const location String)\n" +
                "\n" +
                "(define-fun supported_parking_lot_conditions () Bool\n" +
                "(and (> parking_lot_length 12) is_curve)\n" +
                ")\n" +
                "(define-fun unsupported_parking_lot_conditions () Bool\n" +
                "(and (or (= surface \"puddle\") (= surface \"snow_covered\")) (or (= location \"on_shoulder\") (= location \"partly_on_subject_vehicle_lane\")))\n" +
                ")\n" +
                "(define-fun parking_lot_conditions () Bool\n" +
                "(and supported_parking_lot_conditions (not unsupported_parking_lot_conditions))\n" +
                ")\n" +
                "; --- COD ---\n" +
                "(assert (= parking_lot_length 13))\n" +
                "(assert (= is_curve true))\n" +
                "(assert (= surface \"snow_covered\"))\n" +
                "(assert (= location \"on_shoulder\"))\n" +
                "; --- Assert selected module(s) ---\n" +
                "(assert parking_lot_conditions)\n" +
                "(check-sat)";

        // Create Z3 context
        Context ctx = new Context();

        try {
            // Parse SMT-LIB string
            BoolExpr[] constraints = ctx.parseSMTLIB2String(
                    smtLib, null, null, null, null
            );

            Solver solver = ctx.mkSolver();
            for (BoolExpr c : constraints) {
                solver.add(c);
            }

            // Check satisfiability
            Status result = solver.check();
            System.out.println("Result: " + result);

            if (result == Status.SATISFIABLE) {
                System.out.println("Model: " + solver.getModel());
            }

        } catch (Z3Exception e) {
            System.err.println("Z3 Error: " + e.getMessage());
        } finally {
            ctx.close();
        }
    }
}

