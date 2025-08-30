package odd;// Generated from /Users/basselrafie/Documents/GitHub/odd_compiler/src/main/java/ODD.g4 by ANTLR 4.13.1
import org.antlr.v4.runtime.tree.ParseTreeVisitor;

/**
 * This interface defines a complete generic visitor for a parse tree produced
 * by {@link ODDParser}.
 *
 * @param <T> The return type of the visit operation. Use {@link Void} for
 * operations with no return type.
 */
public interface ODDVisitor<T> extends ParseTreeVisitor<T> {
	/**
	 * Visit a parse tree produced by {@link ODDParser#input}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInput(ODDParser.InputContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#module}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitModule(ODDParser.ModuleContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#logicalexpression}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitLogicalexpression(ODDParser.LogicalexpressionContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#include_and}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInclude_and(ODDParser.Include_andContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#include_or}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitInclude_or(ODDParser.Include_orContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#exclude_and}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExclude_and(ODDParser.Exclude_andContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#exclude_or}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitExclude_or(ODDParser.Exclude_orContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#statement}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitStatement(ODDParser.StatementContext ctx);
	/**
	 * Visit a parse tree produced by {@link ODDParser#condition}.
	 * @param ctx the parse tree
	 * @return the visitor result
	 */
	T visitCondition(ODDParser.ConditionContext ctx);
}