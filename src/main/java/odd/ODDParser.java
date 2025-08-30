package odd;// Generated from /Users/basselrafie/Documents/GitHub/odd_compiler/src/main/java/ODD.g4 by ANTLR 4.13.1
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue"})
public class ODDParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		RELATIONALOPERATOR=1, TAB=2, DTAB=3, TTAB=4, MINUS=5, INTEGER=6, DECIMAL=7, 
		MEASURMENT=8, TRUE=9, FALSE=10, INCLUDE_AND=11, INCLUDE_OR=12, EXCLUDE_AND=13, 
		EXCLUDE_OR=14, ALPHANUMERIC=15, ID=16, BOOL=17, INT=18, DEC=19, STR=20, 
		MODULE_ID_REF=21, WS=22;
	public static final int
		RULE_input = 0, RULE_module = 1, RULE_logicalexpression = 2, RULE_include_and = 3, 
		RULE_include_or = 4, RULE_exclude_and = 5, RULE_exclude_or = 6, RULE_statement = 7, 
		RULE_condition = 8;
	private static String[] makeRuleNames() {
		return new String[] {
                "veriodd/input", "module", "logicalexpression", "include_and", "include_or",
			"exclude_and", "exclude_or", "statement", "condition"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, null, "'    '", "'        '", "'            '", "'-'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, "RELATIONALOPERATOR", "TAB", "DTAB", "TTAB", "MINUS", "INTEGER", 
			"DECIMAL", "MEASURMENT", "TRUE", "FALSE", "INCLUDE_AND", "INCLUDE_OR", 
			"EXCLUDE_AND", "EXCLUDE_OR", "ALPHANUMERIC", "ID", "BOOL", "INT", "DEC", 
			"STR", "MODULE_ID_REF", "WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "odd/ODD.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public ODDParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class InputContext extends ParserRuleContext {
		public List<ModuleContext> module() {
			return getRuleContexts(ModuleContext.class);
		}
		public ModuleContext module(int i) {
			return getRuleContext(ModuleContext.class,i);
		}
		public TerminalNode EOF() { return getToken(ODDParser.EOF, 0); }
		public InputContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_input; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitInput(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InputContext input() throws RecognitionException {
		InputContext _localctx = new InputContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_input);
		int _la;
		try {
			setState(24);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
			case MODULE_ID_REF:
				enterOuterAlt(_localctx, 1);
				{
				setState(19); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(18);
					module();
					}
					}
					setState(21); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID || _la==MODULE_ID_REF );
				}
				break;
			case EOF:
				enterOuterAlt(_localctx, 2);
				{
				setState(23);
				match(EOF);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ModuleContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(ODDParser.ID, 0); }
		public List<LogicalexpressionContext> logicalexpression() {
			return getRuleContexts(LogicalexpressionContext.class);
		}
		public LogicalexpressionContext logicalexpression(int i) {
			return getRuleContext(LogicalexpressionContext.class,i);
		}
		public StatementContext statement() {
			return getRuleContext(StatementContext.class,0);
		}
		public ModuleContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_module; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitModule(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ModuleContext module() throws RecognitionException {
		ModuleContext _localctx = new ModuleContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_module);
		int _la;
		try {
			setState(33);
			_errHandler.sync(this);
			switch ( getInterpreter().adaptivePredict(_input,3,_ctx) ) {
			case 1:
				enterOuterAlt(_localctx, 1);
				{
				setState(26);
				match(ID);
				setState(28); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(27);
					logicalexpression();
					}
					}
					setState(30); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & 30720L) != 0) );
				}
				break;
			case 2:
				enterOuterAlt(_localctx, 2);
				{
				setState(32);
				statement();
				}
				break;
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class LogicalexpressionContext extends ParserRuleContext {
		public Include_andContext include_and() {
			return getRuleContext(Include_andContext.class,0);
		}
		public Include_orContext include_or() {
			return getRuleContext(Include_orContext.class,0);
		}
		public Exclude_andContext exclude_and() {
			return getRuleContext(Exclude_andContext.class,0);
		}
		public Exclude_orContext exclude_or() {
			return getRuleContext(Exclude_orContext.class,0);
		}
		public LogicalexpressionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_logicalexpression; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitLogicalexpression(this);
			else return visitor.visitChildren(this);
		}
	}

	public final LogicalexpressionContext logicalexpression() throws RecognitionException {
		LogicalexpressionContext _localctx = new LogicalexpressionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_logicalexpression);
		try {
			setState(39);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case INCLUDE_AND:
				enterOuterAlt(_localctx, 1);
				{
				setState(35);
				include_and();
				}
				break;
			case INCLUDE_OR:
				enterOuterAlt(_localctx, 2);
				{
				setState(36);
				include_or();
				}
				break;
			case EXCLUDE_AND:
				enterOuterAlt(_localctx, 3);
				{
				setState(37);
				exclude_and();
				}
				break;
			case EXCLUDE_OR:
				enterOuterAlt(_localctx, 4);
				{
				setState(38);
				exclude_or();
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class Include_andContext extends ParserRuleContext {
		public TerminalNode INCLUDE_AND() { return getToken(ODDParser.INCLUDE_AND, 0); }
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public Include_andContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_include_and; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitInclude_and(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Include_andContext include_and() throws RecognitionException {
		Include_andContext _localctx = new Include_andContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_include_and);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(41);
			match(INCLUDE_AND);
			setState(43); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(42);
					statement();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(45); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,5,_ctx);
			} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class Include_orContext extends ParserRuleContext {
		public TerminalNode INCLUDE_OR() { return getToken(ODDParser.INCLUDE_OR, 0); }
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public Include_orContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_include_or; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitInclude_or(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Include_orContext include_or() throws RecognitionException {
		Include_orContext _localctx = new Include_orContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_include_or);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(47);
			match(INCLUDE_OR);
			setState(49); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(48);
					statement();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(51); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
			} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class Exclude_andContext extends ParserRuleContext {
		public TerminalNode EXCLUDE_AND() { return getToken(ODDParser.EXCLUDE_AND, 0); }
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public Exclude_andContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exclude_and; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitExclude_and(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Exclude_andContext exclude_and() throws RecognitionException {
		Exclude_andContext _localctx = new Exclude_andContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_exclude_and);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(53);
			match(EXCLUDE_AND);
			setState(55); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(54);
					statement();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(57); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
			} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class Exclude_orContext extends ParserRuleContext {
		public TerminalNode EXCLUDE_OR() { return getToken(ODDParser.EXCLUDE_OR, 0); }
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public Exclude_orContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_exclude_or; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitExclude_or(this);
			else return visitor.visitChildren(this);
		}
	}

	public final Exclude_orContext exclude_or() throws RecognitionException {
		Exclude_orContext _localctx = new Exclude_orContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_exclude_or);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(59);
			match(EXCLUDE_OR);
			setState(61); 
			_errHandler.sync(this);
			_alt = 1;
			do {
				switch (_alt) {
				case 1:
					{
					{
					setState(60);
					statement();
					}
					}
					break;
				default:
					throw new NoViableAltException(this);
				}
				setState(63); 
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,8,_ctx);
			} while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER );
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class StatementContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(ODDParser.ID, 0); }
		public List<ConditionContext> condition() {
			return getRuleContexts(ConditionContext.class);
		}
		public ConditionContext condition(int i) {
			return getRuleContext(ConditionContext.class,i);
		}
		public TerminalNode MODULE_ID_REF() { return getToken(ODDParser.MODULE_ID_REF, 0); }
		public StatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statement; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StatementContext statement() throws RecognitionException {
		StatementContext _localctx = new StatementContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_statement);
		int _la;
		try {
			setState(72);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				enterOuterAlt(_localctx, 1);
				{
				setState(65);
				match(ID);
				setState(67); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(66);
					condition();
					}
					}
					setState(69); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & 1966080L) != 0) );
				}
				break;
			case MODULE_ID_REF:
				enterOuterAlt(_localctx, 2);
				{
				setState(71);
				match(MODULE_ID_REF);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	@SuppressWarnings("CheckReturnValue")
	public static class ConditionContext extends ParserRuleContext {
		public TerminalNode BOOL() { return getToken(ODDParser.BOOL, 0); }
		public TerminalNode INT() { return getToken(ODDParser.INT, 0); }
		public TerminalNode DEC() { return getToken(ODDParser.DEC, 0); }
		public TerminalNode STR() { return getToken(ODDParser.STR, 0); }
		public ConditionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_condition; }
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof ODDVisitor ) return ((ODDVisitor<? extends T>)visitor).visitCondition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConditionContext condition() throws RecognitionException {
		ConditionContext _localctx = new ConditionContext(_ctx, getState());
		enterRule(_localctx, 16, RULE_condition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(74);
			_la = _input.LA(1);
			if ( !((((_la) & ~0x3f) == 0 && ((1L << _la) & 1966080L) != 0)) ) {
			_errHandler.recoverInline(this);
			}
			else {
				if ( _input.LA(1)==Token.EOF ) matchedEOF = true;
				_errHandler.reportMatch(this);
				consume();
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0016M\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001\u0002"+
		"\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004\u0002"+
		"\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007\u0002"+
		"\b\u0007\b\u0001\u0000\u0004\u0000\u0014\b\u0000\u000b\u0000\f\u0000\u0015"+
		"\u0001\u0000\u0003\u0000\u0019\b\u0000\u0001\u0001\u0001\u0001\u0004\u0001"+
		"\u001d\b\u0001\u000b\u0001\f\u0001\u001e\u0001\u0001\u0003\u0001\"\b\u0001"+
		"\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0003\u0002(\b\u0002"+
		"\u0001\u0003\u0001\u0003\u0004\u0003,\b\u0003\u000b\u0003\f\u0003-\u0001"+
		"\u0004\u0001\u0004\u0004\u00042\b\u0004\u000b\u0004\f\u00043\u0001\u0005"+
		"\u0001\u0005\u0004\u00058\b\u0005\u000b\u0005\f\u00059\u0001\u0006\u0001"+
		"\u0006\u0004\u0006>\b\u0006\u000b\u0006\f\u0006?\u0001\u0007\u0001\u0007"+
		"\u0004\u0007D\b\u0007\u000b\u0007\f\u0007E\u0001\u0007\u0003\u0007I\b"+
		"\u0007\u0001\b\u0001\b\u0001\b\u0000\u0000\t\u0000\u0002\u0004\u0006\b"+
		"\n\f\u000e\u0010\u0000\u0001\u0001\u0000\u0011\u0014P\u0000\u0018\u0001"+
		"\u0000\u0000\u0000\u0002!\u0001\u0000\u0000\u0000\u0004\'\u0001\u0000"+
		"\u0000\u0000\u0006)\u0001\u0000\u0000\u0000\b/\u0001\u0000\u0000\u0000"+
		"\n5\u0001\u0000\u0000\u0000\f;\u0001\u0000\u0000\u0000\u000eH\u0001\u0000"+
		"\u0000\u0000\u0010J\u0001\u0000\u0000\u0000\u0012\u0014\u0003\u0002\u0001"+
		"\u0000\u0013\u0012\u0001\u0000\u0000\u0000\u0014\u0015\u0001\u0000\u0000"+
		"\u0000\u0015\u0013\u0001\u0000\u0000\u0000\u0015\u0016\u0001\u0000\u0000"+
		"\u0000\u0016\u0019\u0001\u0000\u0000\u0000\u0017\u0019\u0005\u0000\u0000"+
		"\u0001\u0018\u0013\u0001\u0000\u0000\u0000\u0018\u0017\u0001\u0000\u0000"+
		"\u0000\u0019\u0001\u0001\u0000\u0000\u0000\u001a\u001c\u0005\u0010\u0000"+
		"\u0000\u001b\u001d\u0003\u0004\u0002\u0000\u001c\u001b\u0001\u0000\u0000"+
		"\u0000\u001d\u001e\u0001\u0000\u0000\u0000\u001e\u001c\u0001\u0000\u0000"+
		"\u0000\u001e\u001f\u0001\u0000\u0000\u0000\u001f\"\u0001\u0000\u0000\u0000"+
		" \"\u0003\u000e\u0007\u0000!\u001a\u0001\u0000\u0000\u0000! \u0001\u0000"+
		"\u0000\u0000\"\u0003\u0001\u0000\u0000\u0000#(\u0003\u0006\u0003\u0000"+
		"$(\u0003\b\u0004\u0000%(\u0003\n\u0005\u0000&(\u0003\f\u0006\u0000\'#"+
		"\u0001\u0000\u0000\u0000\'$\u0001\u0000\u0000\u0000\'%\u0001\u0000\u0000"+
		"\u0000\'&\u0001\u0000\u0000\u0000(\u0005\u0001\u0000\u0000\u0000)+\u0005"+
		"\u000b\u0000\u0000*,\u0003\u000e\u0007\u0000+*\u0001\u0000\u0000\u0000"+
		",-\u0001\u0000\u0000\u0000-+\u0001\u0000\u0000\u0000-.\u0001\u0000\u0000"+
		"\u0000.\u0007\u0001\u0000\u0000\u0000/1\u0005\f\u0000\u000002\u0003\u000e"+
		"\u0007\u000010\u0001\u0000\u0000\u000023\u0001\u0000\u0000\u000031\u0001"+
		"\u0000\u0000\u000034\u0001\u0000\u0000\u00004\t\u0001\u0000\u0000\u0000"+
		"57\u0005\r\u0000\u000068\u0003\u000e\u0007\u000076\u0001\u0000\u0000\u0000"+
		"89\u0001\u0000\u0000\u000097\u0001\u0000\u0000\u00009:\u0001\u0000\u0000"+
		"\u0000:\u000b\u0001\u0000\u0000\u0000;=\u0005\u000e\u0000\u0000<>\u0003"+
		"\u000e\u0007\u0000=<\u0001\u0000\u0000\u0000>?\u0001\u0000\u0000\u0000"+
		"?=\u0001\u0000\u0000\u0000?@\u0001\u0000\u0000\u0000@\r\u0001\u0000\u0000"+
		"\u0000AC\u0005\u0010\u0000\u0000BD\u0003\u0010\b\u0000CB\u0001\u0000\u0000"+
		"\u0000DE\u0001\u0000\u0000\u0000EC\u0001\u0000\u0000\u0000EF\u0001\u0000"+
		"\u0000\u0000FI\u0001\u0000\u0000\u0000GI\u0005\u0015\u0000\u0000HA\u0001"+
		"\u0000\u0000\u0000HG\u0001\u0000\u0000\u0000I\u000f\u0001\u0000\u0000"+
		"\u0000JK\u0007\u0000\u0000\u0000K\u0011\u0001\u0000\u0000\u0000\u000b"+
		"\u0015\u0018\u001e!\'-39?EH";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}