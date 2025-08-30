package cod;

import java.util.stream.Collectors;

public class CODVisitorSMTLIB extends CODBaseVisitor<String>{

    @Override
    public String visitInput(CODParser.InputContext ctx) {
        // Join each statement's translation with newlines
        return ctx.statement().stream()
                .map(this::visit)
                .collect(Collectors.joining("\n"));
    }

    @Override
    public String visitStatement(CODParser.StatementContext ctx) {
        String name = ctx.ID().getText().replace(":","");
        String value = visit(ctx.condition()).replace("=","");
        return "(assert (= " + name + " " + value + "))";
    }

    @Override
    public String visitCondition(CODParser.ConditionContext ctx) {
        if (ctx.BOOL() != null) {
            return ctx.BOOL().getText();
        }
        if (ctx.INT() != null) {
            return ctx.INT().getText();
        }
        if (ctx.DEC() != null) {
            return ctx.DEC().getText();
        }
        if (ctx.STR() != null) {
            // STR is bare -> add quotes
            String raw = ctx.STR().getText();
            return "\"" + raw + "\"";
        }
        // Fallback (shouldn't happen with your grammar)
        return "\"\"";
    }



//    @Override
//    public String visitStatement(CODParser.StatementContext ctx) {
//
//        String name = ctx.ID().getText();
//        String value = visit(ctx.condition());
//        return "(assert (= " + name + " " + value + "))";
//
//    }
}
