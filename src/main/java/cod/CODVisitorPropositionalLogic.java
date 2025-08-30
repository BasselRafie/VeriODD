package cod;

import java.util.stream.Collectors;

public class CODVisitorPropositionalLogic extends CODBaseVisitor<String> {

    @Override
    public String visitInput(CODParser.InputContext ctx) {
        // Join each statement on its own line
        return ctx.statement().stream()
                .map(this::visit)
                .collect(Collectors.joining("\n"));
    }

    @Override
    public String visitStatement(CODParser.StatementContext ctx) {
        // Strip the trailing ':' from the key and any stray '=' from the value
        String name  = ctx.ID().getText().replace(":", "").trim();
        String value = visit(ctx.condition()).replace("=", "").trim();
        return name + " = " + value;
    }

    @Override
    public String visitCondition(CODParser.ConditionContext ctx) {
        if (ctx.BOOL() != null) return ctx.BOOL().getText();
        if (ctx.INT()  != null) return ctx.INT().getText();
        if (ctx.DEC()  != null) return ctx.DEC().getText();
        if (ctx.STR()  != null) return ctx.STR().getText(); // bare (no quotes)
        return "";
    }
}