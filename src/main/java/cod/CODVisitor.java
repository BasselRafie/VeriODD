package cod;// Generated from C:/Users/br17/Documents/GitHub/odd_compiler/src/main/java/COD.g4 by ANTLR 4.13.2
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link CODParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface CODVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link CODParser#input}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInput(CODParser.InputContext ctx);
	/**
	 * Visit a parse tree produced by {@link CODParser#statement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStatement(CODParser.StatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link CODParser#condition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCondition(CODParser.ConditionContext ctx);
}