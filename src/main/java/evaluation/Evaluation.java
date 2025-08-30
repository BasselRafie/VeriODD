package evaluation;

import com.microsoft.z3.*;
import java.util.*;
import java.nio.file.*;
import java.io.IOException;
import static java.lang.System.nanoTime;
import veriodd.VeriODD;

public final class Evaluation {

    // Batch sizes and repetitions
    static final int[] BATCH_SIZES = {10, 50, 100, 500, 1000, 2000, 5000};
    static final int REPEATS = 5;

    // Toggle model extraction during perf runs (false avoids overhead)
    static final boolean GET_MODEL = false;

    static final String SMALL_ODD_PATH = "C:\\Users\\br17\\Documents\\GitHub\\odd_compiler\\src\\main\\java\\evaluation\\odd_4.yaml";

    // Path to your 1000-variable ODD file (adjust if needed)
    static final String LARGE_ODD_PATH = "C:\\Users\\br17\\Documents\\GitHub\\odd_compiler\\src\\main\\java\\evaluation\\odd_1000.yaml";

    public static void main(String[] args) throws Exception {
        // ---- SMALL ODD (parking lot) ----
        String oddYamlSmall = readAll(SMALL_ODD_PATH);

        // ---- LARGE ODD: load the 1000-variable ODD from file; top module is "big_odd" ----
        String oddYamlLarge = readAll(LARGE_ODD_PATH);

        // COD datasets (matching each ODD)
        List<String> codsSmall = generateCODsSmall(6000);
        List<String> codsLarge = generateCODsLarge1000(6000); // each COD assigns all 1000 vars

        // Run small ODD (top module: parking_lot_conditions)
        runOneODD("SMALL", oddYamlSmall, codsSmall, List.of("parking_lot_conditions"));

        // Run large ODD (top module: big_odd)
        runOneODD("LARGE(1000-vars)", oddYamlLarge, codsLarge, List.of("big_odd"));
    }

    // ---------- Harness ----------

    static void runOneODD(String name, String oddYaml, List<String> allCODs, List<String> modules) throws Exception {
        System.out.println("\n== ODD " + name + " ==");
        for (int n : BATCH_SIZES) {
            bench(oddYaml, allCODs.subList(0, n), modules, REPEATS);
        }
    }

    static void bench(String oddYaml, List<String> codBatch, List<String> modules, int repeats) throws Exception {
        long tTransOdd = 0, tTotal = 0;
        for (int r = 0; r < repeats; r++) {
            // ODD -> SMT-LIB (one-time per run)
            long t0 = nanoTime();
            String oddSmt = VeriODD.Translators.translateToSmtLib(oddYaml, "odd");
            long t1 = nanoTime();
            tTransOdd += (t1 - t0);

            long start = nanoTime();
            // Baseline: fresh solver per COD
            for (String codYaml : codBatch) {
                String codSmt = VeriODD.Translators.translateToSmtLib(codYaml, "cod");
                String script = assemble(oddSmt, codSmt, modules, true, GET_MODEL);
                solveOnce(script);
            }
            tTotal += (nanoTime() - start);
        }
        double avgTransOddMs = tTransOdd / 1e6 / repeats;
        double avgTotalMs    = tTotal    / 1e6 / repeats;
        double avgPerCODMs   = avgTotalMs / codBatch.size();

        System.out.printf(Locale.US,
                "CODs=%d  ODD-translate=%.2f ms  Total=%.2f ms  Avg/COD=%.3f ms%n",
                codBatch.size(), avgTransOddMs, avgTotalMs, avgPerCODMs);
    }

    // ---------- Solver wiring ----------

    static void solveOnce(String scriptWithCmds) throws Exception {
        try (Context ctx = new Context(new HashMap<>())) {
            String cleaned = stripCommands(scriptWithCmds);
            BoolExpr[] cs = ctx.parseSMTLIB2String(cleaned, null, null, null, null);
            Solver s = ctx.mkSolver();
            if (cs != null) for (BoolExpr c : cs) s.add(c);
            Status st = s.check();
            if (GET_MODEL && st == Status.SATISFIABLE) { s.getModel(); }
        }
    }

    // ---------- Assembly & utils ----------

    static String assemble(String oddSmt, String codSmt, List<String> modules,
                           boolean checkSat, boolean getModel) {
        StringBuilder sb = new StringBuilder();
        sb.append("; --- ODD ---\n").append(stripCommands(oddSmt));
        sb.append("; --- COD ---\n").append(stripCommands(codSmt));
        sb.append("; --- Assert module(s) ---\n");
        for (String m : modules) sb.append("(assert ").append(m.replaceAll(":+$", "")).append(")\n");
        if (checkSat) sb.append("(check-sat)\n");
        if (getModel) sb.append("(get-model)\n");
        return sb.toString();
    }

    static String stripCommands(String s) {
        String[] lines = s.replace("\r\n","\n").split("\n");
        StringBuilder sb = new StringBuilder();
        for (String line : lines) {
            String t = line.trim();
            if (t.equals("(check-sat)") || t.equals("(get-model)")) continue;
            sb.append(line).append('\n');
        }
        return sb.toString();
    }

    static String readAll(String path) {
        try {
            return Files.readString(Paths.get(path));
        } catch (IOException e) {
            throw new RuntimeException("Failed to read ODD file: " + path, e);
        }
    }

    // ---------- COD generators ----------

    // Small ODD CODs (parking lot)
    static List<String> generateCODsSmall(int n) {
        List<String> out = new ArrayList<>(n);
        Random rnd = new Random(42);
        String[] surfaces = {"puddle","snow_covered","dry","wet"};
        String[] locations = {"on_shoulder","partly_on_subject_vehicle_lane","in_lane"};
        for (int i = 0; i < n; i++) {
            int len = 8 + rnd.nextInt(15); // 8..22
            String surf = surfaces[rnd.nextInt(surfaces.length)];
            String loc  = locations[rnd.nextInt(locations.length)];
            String cod = ""
                    + "parking_lot_length: = " + len + "\n"
                    + "is_curve: " + (rnd.nextBoolean() ? "true" : "false") + "\n"
                    + "surface: " + surf + "\n"
                    + "location: " + loc + "\n";
            out.add(cod);
        }
        return out;
    }

    // Large ODD CODs — matches the 1000-variable ODD (var_0001..var_1000)
    // Pattern mirrors the generator used for the ODD:
    // i % 3 == 1 -> boolean; i % 3 == 2 -> integer; else -> enum string "state_k"
    static List<String> generateCODsLarge1000(int n) {
        List<String> out = new ArrayList<>(n);
        Random rnd = new Random(12345);

        for (int t = 0; t < n; t++) {
            StringBuilder sb = new StringBuilder();
            for (int i = 1; i <= 1000; i++) {
                String name = String.format("var_%04d", i);
                if (i % 3 == 1) {
                    // boolean
                    sb.append(name).append(": ").append(rnd.nextBoolean() ? "true" : "false").append('\n');
                } else if (i % 3 == 2) {
                    // integer (no units in COD)
                    int val = 5 + rnd.nextInt(100); // 5..104
                    sb.append(name).append(": = ").append(val).append('\n');
                } else {
                    // enum-like state string (unquoted bare identifier)
                    int state = 1 + rnd.nextInt(5); // state_1..state_5
                    sb.append(name).append(": state_").append(state).append('\n');
                }
            }
            out.add(sb.toString());
        }
        return out;
    }
}
