package odd;

import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.ParseTree;

public class MainODD {
    public static void main(String[] args) {


        String inputString= "supported_parking_lot_conditions:\n" +
                "    INCLUDE_AND:\n" +
                "        parking_lot_length: > 12 m\n" +
                "        is_curve: true\n" +
                "\n" +
                "unsupported_parking_lot_conditions:\n" +
                "    INCLUDE_AND:\n" +
                "        surface:\n" +
                "            - puddle\n" +
                "            - snow_covered\n" +
                "        location:\n" +
                "            - on_shoulder\n" +
                "            - partly_on_subject_vehicle_lane\n" +
                "\n" +
                "parking_lot_conditions:\n" +
                "    INCLUDE_AND:\n" +
                "        - supported_parking_lot_conditions\n" +
                "    EXCLUDE_OR:\n" +
                "        - unsupported_parking_lot_conditions";
        CodePointCharStream input = CharStreams.fromString(inputString);
        ODDLexer lexer = new ODDLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ODDParser parser = new ODDParser(tokens);
        ParseTree tree = parser.input();

        ODDVistorSMTLIB ODDVistorSMTLIB = new ODDVistorSMTLIB();
        ODDVisitorPropositionalLogic ODDVisitorPropositionalLogic = new ODDVisitorPropositionalLogic();

        String resultSMTLIB = ODDVistorSMTLIB.visit(tree);
        String resultPropositionalLogic = ODDVisitorPropositionalLogic.visit(tree);

       System.out.println(resultSMTLIB);
       //System.out.println(resultPropositionalLogic);

    }
}