package cod;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CodePointCharStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

public class MainCOD {

    public static void main(String[] args) {

        String inputString =
            "parking_lot_length: = 13\n" +
                    "is_curve: true\n" +
                    "surface: snow_covered\n" +
                    "location: on_shoulder";
        CodePointCharStream input = CharStreams.fromString(inputString);
        CODLexer lexer = new CODLexer(input);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        CODParser parser = new CODParser(tokens);
        ParseTree tree = parser.input();

        CODVisitorSMTLIB myVistorSMTLIB = new CODVisitorSMTLIB();

        CODVisitorPropositionalLogic myVistorPropositionalLogic = new CODVisitorPropositionalLogic();

        String resultPropositionalLogic = myVistorPropositionalLogic.visit(tree);

        String resultSMTLIB = myVistorSMTLIB.visit(tree);

        //System.out.println(resultSMTLIB);

        System.out.println(resultPropositionalLogic);

    }
}
