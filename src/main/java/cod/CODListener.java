package cod;// Generated from C:/Users/br17/Documents/GitHub/odd_compiler/src/main/java/COD.g4 by ANTLR 4.13.2
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link CODParser}.
 */
public interface CODListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link CODParser#input}.
	 * @param ctx the parse tree
	 */
	void enterInput(CODParser.InputContext ctx);
	/**
	 * Exit a parse tree produced by {@link CODParser#input}.
	 * @param ctx the parse tree
	 */
	void exitInput(CODParser.InputContext ctx);
	/**
	 * Enter a parse tree produced by {@link CODParser#statement}.
	 * @param ctx the parse tree
	 */
	void enterStatement(CODParser.StatementContext ctx);
	/**
	 * Exit a parse tree produced by {@link CODParser#statement}.
	 * @param ctx the parse tree
	 */
	void exitStatement(CODParser.StatementContext ctx);
	/**
	 * Enter a parse tree produced by {@link CODParser#condition}.
	 * @param ctx the parse tree
	 */
	void enterCondition(CODParser.ConditionContext ctx);
	/**
	 * Exit a parse tree produced by {@link CODParser#condition}.
	 * @param ctx the parse tree
	 */
	void exitCondition(CODParser.ConditionContext ctx);
}