// Generated from C:/Users/br17/Documents/GitHub/odd_compiler/src/main/java/COD.g4 by ANTLR 4.13.2
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue", "this-escape"})
public class CODParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.13.2", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		RELATIONALOPERATOR=1, TAB=2, DTAB=3, TTAB=4, MINUS=5, INTEGER=6, DECIMAL=7, 
		MEASURMENT=8, TRUE=9, FALSE=10, INCLUDE_AND=11, INCLUDE_OR=12, EXCLUDE_AND=13, 
		EXCLUDE_OR=14, ALPHANUMERIC=15, ID=16, BOOL=17, INT=18, DEC=19, STR=20, 
		MODULE_ID_REF=21, WS=22;
	public static final int
		RULE_input = 0, RULE_statement = 1, RULE_condition = 2;
	private static String[] makeRuleNames() {
		return new String[] {
                "veriodd/input", "statement", "condition"
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
	public String getGrammarFileName() { return "cod/COD.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public CODParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@SuppressWarnings("CheckReturnValue")
	public static class InputContext extends ParserRuleContext {
		public List<StatementContext> statement() {
			return getRuleContexts(StatementContext.class);
		}
		public StatementContext statement(int i) {
			return getRuleContext(StatementContext.class,i);
		}
		public TerminalNode EOF() { return getToken(CODParser.EOF, 0); }
		public InputContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_input; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).enterInput(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).exitInput(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof CODVisitor ) return ((CODVisitor<? extends T>)visitor).visitInput(this);
			else return visitor.visitChildren(this);
		}
	}

	public final InputContext input() throws RecognitionException {
		InputContext _localctx = new InputContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_input);
		int _la;
		try {
			setState(12);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
			case MODULE_ID_REF:
				enterOuterAlt(_localctx, 1);
				{
				setState(7); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(6);
					statement();
					}
					}
					setState(9); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( _la==ID || _la==MODULE_ID_REF );
				}
				break;
			case EOF:
				enterOuterAlt(_localctx, 2);
				{
				setState(11);
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
	public static class StatementContext extends ParserRuleContext {
		public TerminalNode ID() { return getToken(CODParser.ID, 0); }
		public List<ConditionContext> condition() {
			return getRuleContexts(ConditionContext.class);
		}
		public ConditionContext condition(int i) {
			return getRuleContext(ConditionContext.class,i);
		}
		public TerminalNode MODULE_ID_REF() { return getToken(CODParser.MODULE_ID_REF, 0); }
		public StatementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_statement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).enterStatement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).exitStatement(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof CODVisitor ) return ((CODVisitor<? extends T>)visitor).visitStatement(this);
			else return visitor.visitChildren(this);
		}
	}

	public final StatementContext statement() throws RecognitionException {
		StatementContext _localctx = new StatementContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_statement);
		int _la;
		try {
			setState(21);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				enterOuterAlt(_localctx, 1);
				{
				setState(14);
				match(ID);
				setState(16); 
				_errHandler.sync(this);
				_la = _input.LA(1);
				do {
					{
					{
					setState(15);
					condition();
					}
					}
					setState(18); 
					_errHandler.sync(this);
					_la = _input.LA(1);
				} while ( (((_la) & ~0x3f) == 0 && ((1L << _la) & 1966080L) != 0) );
				}
				break;
			case MODULE_ID_REF:
				enterOuterAlt(_localctx, 2);
				{
				setState(20);
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
		public TerminalNode BOOL() { return getToken(CODParser.BOOL, 0); }
		public TerminalNode INT() { return getToken(CODParser.INT, 0); }
		public TerminalNode DEC() { return getToken(CODParser.DEC, 0); }
		public TerminalNode STR() { return getToken(CODParser.STR, 0); }
		public ConditionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_condition; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).enterCondition(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof CODListener ) ((CODListener)listener).exitCondition(this);
		}
		@Override
		public <T> T accept(ParseTreeVisitor<? extends T> visitor) {
			if ( visitor instanceof CODVisitor ) return ((CODVisitor<? extends T>)visitor).visitCondition(this);
			else return visitor.visitChildren(this);
		}
	}

	public final ConditionContext condition() throws RecognitionException {
		ConditionContext _localctx = new ConditionContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_condition);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(23);
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
		"\u0004\u0001\u0016\u001a\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0001\u0000\u0004\u0000\b\b\u0000\u000b\u0000"+
		"\f\u0000\t\u0001\u0000\u0003\u0000\r\b\u0000\u0001\u0001\u0001\u0001\u0004"+
		"\u0001\u0011\b\u0001\u000b\u0001\f\u0001\u0012\u0001\u0001\u0003\u0001"+
		"\u0016\b\u0001\u0001\u0002\u0001\u0002\u0001\u0002\u0000\u0000\u0003\u0000"+
		"\u0002\u0004\u0000\u0001\u0001\u0000\u0011\u0014\u001a\u0000\f\u0001\u0000"+
		"\u0000\u0000\u0002\u0015\u0001\u0000\u0000\u0000\u0004\u0017\u0001\u0000"+
		"\u0000\u0000\u0006\b\u0003\u0002\u0001\u0000\u0007\u0006\u0001\u0000\u0000"+
		"\u0000\b\t\u0001\u0000\u0000\u0000\t\u0007\u0001\u0000\u0000\u0000\t\n"+
		"\u0001\u0000\u0000\u0000\n\r\u0001\u0000\u0000\u0000\u000b\r\u0005\u0000"+
		"\u0000\u0001\f\u0007\u0001\u0000\u0000\u0000\f\u000b\u0001\u0000\u0000"+
		"\u0000\r\u0001\u0001\u0000\u0000\u0000\u000e\u0010\u0005\u0010\u0000\u0000"+
		"\u000f\u0011\u0003\u0004\u0002\u0000\u0010\u000f\u0001\u0000\u0000\u0000"+
		"\u0011\u0012\u0001\u0000\u0000\u0000\u0012\u0010\u0001\u0000\u0000\u0000"+
		"\u0012\u0013\u0001\u0000\u0000\u0000\u0013\u0016\u0001\u0000\u0000\u0000"+
		"\u0014\u0016\u0005\u0015\u0000\u0000\u0015\u000e\u0001\u0000\u0000\u0000"+
		"\u0015\u0014\u0001\u0000\u0000\u0000\u0016\u0003\u0001\u0000\u0000\u0000"+
		"\u0017\u0018\u0007\u0000\u0000\u0000\u0018\u0005\u0001\u0000\u0000\u0000"+
		"\u0004\t\f\u0012\u0015";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}