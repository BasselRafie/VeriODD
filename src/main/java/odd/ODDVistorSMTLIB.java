package odd;

import org.antlr.v4.runtime.tree.ParseTree;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ODDVistorSMTLIB extends ODDBaseVisitor<String>{

    private String constants = "";
    private String result= "";
    private String moduleResult = "";
    private int expressionsCount =  0;
    private final ArrayList<String> modulesArrayList = new ArrayList<String>();
    private final ArrayList<String> constantsArrayList = new ArrayList<String>();
    private final LinkedHashMap<String, String> modulesHashmap = new LinkedHashMap<String, String>();

    @Override
    public String visitInput(ODDParser.InputContext ctx) {

//        for (int i = ctx.getChildCount() - 1; i >= 0; i--) {
//            ParseTree child = ctx.getChild(i);
//            child.accept(this); // Visit the child
//        }
        for (int i = 0; i < ctx.getChildCount(); i++) {
            ParseTree child = ctx.getChild(i);
            child.accept(this); // Visit the child
        }
        return constants + "\n" + result;
    }

    @Override
    public String visitModule(ODDParser.ModuleContext ctx) {

        expressionsCount = ctx.getChildCount();
        boolean multipleExpressions = expressionsCount > 2;
        String moduleName ="";
        if(ctx.statement() != null){moduleName=ctx.statement().ID().getText().replace(":","");
            moduleResult += visitStatement(ctx.statement());
            modulesHashmap.put(moduleName,moduleResult);
            return result += "(assert " + moduleResult + ")";
        }
        else{moduleName = ctx.getChild(0).getText().replace(":", "");
            modulesArrayList.add(moduleName);
            moduleResult = multipleExpressions?"(define-fun " +moduleName+ " () Bool\n(and ":"(define-fun " + moduleName + " () Bool\n";
            visitChildren(ctx);
        }
        moduleResult += multipleExpressions?")\n)\n":"\n)\n";
        return result += moduleResult;
    }

    @Override
    public String visitInclude_and(ODDParser.Include_andContext ctx) {
        int childCount = ctx.getChildCount();
        boolean multipleStatements = childCount>2;
        String include_and = multipleStatements?"(and ":"";
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
                if (i != childCount - 1) {
                    include_and +=  child.accept(this) + " ";
                } else{
                    include_and += multipleStatements?child.accept(this) + ")":child.accept(this);
                }
            }
        expressionsCount --;
        return  moduleResult += expressionsCount==1?include_and:include_and+" ";
    }

    @Override
    public String visitInclude_or(ODDParser.Include_orContext ctx) {
        int childCount = ctx.getChildCount();
        boolean multipleStatements = childCount>2;
        String include_or = multipleStatements?"(or ":"";
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
            if (i != childCount - 1) {
                include_or +=  child.accept(this) + " ";
            } else{
                include_or += multipleStatements?child.accept(this) + ")":child.accept(this);
            }
        }
        expressionsCount --;
        return  moduleResult += expressionsCount==1?include_or:include_or+" ";
    }
    @Override
    public String visitExclude_and(ODDParser.Exclude_andContext ctx) {

        int childCount = ctx.getChildCount();
        boolean multipleStatements = childCount>2;
        String exclude_and = multipleStatements?"(not (and ":"(not ";

        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
            if (i != childCount - 1) {
                exclude_and +=  child.accept(this) + " ";
            } else{
                exclude_and += multipleStatements?child.accept(this) + "))":child.accept(this) + ")";
            }
        }
        expressionsCount --;
        return  moduleResult += expressionsCount==1?exclude_and:exclude_and+" ";
    }

    @Override
    public String visitExclude_or(ODDParser.Exclude_orContext ctx) {

        int childCount = ctx.getChildCount();
        boolean multipleStatements = childCount>2;
        String exclude_or = multipleStatements?"(not (or ":"(not ";

        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
                if (i != childCount - 1) {
                    exclude_or +=  child.accept(this) + " ";
                } else{
                    exclude_or += multipleStatements?child.accept(this) + "))":child.accept(this) + ")";
                }
            }
        expressionsCount --;
        return  moduleResult += expressionsCount==1?exclude_or:exclude_or+" ";
    }

    @Override
    public String visitStatement(ODDParser.StatementContext ctx) {
        int childCount = ctx.getChildCount();
        boolean multipleStatements = childCount > 2;
        String currentStatement = multipleStatements ? "(or " : "";

        //  1 child case
        if (ctx.getChildCount() ==1){
            if(!constantsArrayList.contains(ctx.getText()) && !modulesArrayList.contains(ctx.getText())) {
                constants += declareConstant(ctx.getText());
                constantsArrayList.addAll(getStatementIDs(ctx.getText()));
            }
            return currentStatement += translateStatementToSMTLIB(ctx.getText());
        }
        //multiple child case
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child0 = ctx.getChild(0);
            org.antlr.v4.runtime.tree.ParseTree childI = ctx.getChild(i);
            String statement = child0.getText() + childI.getText();
            if (childI.getText().contains(".") && !constantsArrayList.contains(child0.getText())) {
                constants += declareConstant(statement);
                constantsArrayList.addAll(getStatementIDs(statement));
                break;
            }
        }
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child0 = ctx.getChild(0);
            org.antlr.v4.runtime.tree.ParseTree childI = ctx.getChild(i);
            String statement = child0.getText() + childI.getText();
            if (!modulesArrayList.containsAll(getStatementIDs(statement)) && !constantsArrayList.containsAll(getStatementIDs(statement))) {
                constants += declareConstant(statement);
                constantsArrayList.addAll(getStatementIDs(statement));
            }
            if (i != ctx.getChildCount() - 1) {
                currentStatement += translateStatementToSMTLIB(statement) + " ";
            } else {
                currentStatement += multipleStatements ? translateStatementToSMTLIB(statement) + ")" : translateStatementToSMTLIB(statement);
            }
        }

        return currentStatement;
    }

    private String declareConstant (String statement) {
            String declareConst = "(declare-const ";
            if (!statement.contains(":")) {
                return declareConst + statement + " Bool)\n";
            }
            String[] parts = statement.split(":");
            if (parts.length == 2) {
                if (parts[1].equalsIgnoreCase("true") | parts[1].equalsIgnoreCase("false")) {
                    return declareConst + parts[0] + " Bool)\n";
                } else if (parts[1].contains("=") | parts[1].contains(">") | parts[1].contains("<")) {
                    if (!parts[1].contains(".")) {
                        return declareConst + parts[0] + " Int)\n";
                    } else {
                        return declareConst + parts[0] + " Real)\n";
                    }
                } else {
                    boolean part0IsNotDeclared = !constantsArrayList.contains(parts[0]) && !modulesArrayList.contains(parts[0]);
                    //boolean part1IsNotDeclared = !constantsArrayList.contains(parts[1]) && !modulesArrayList.contains(parts[1]);
                    return (part0IsNotDeclared ? declareConst + parts[0] + " String)\n" : "");
                          //  (part1IsNotDeclared ? declareConst + parts[1] + " Bool)\n" : "");
                }
            }
        throw new IllegalArgumentException("Invalid input statement format at " + statement);
    }

    public String translateStatementToSMTLIB(String statement) {
        if(!statement.contains(":")){
            if(modulesHashmap.get(statement) != null){
                return modulesHashmap.get(statement);
            }
            return statement;
        }
        String[] parts = statement.split(":");
        if(modulesHashmap.get(parts[0]) != null){
            parts[0] = modulesHashmap.get(parts[0]);
        } else if (modulesHashmap.get(parts[1]) != null){
            parts[1] = modulesHashmap.get(parts[1]);
            return "(" + "=" + " " + parts[0] + " " + parts[1] + ")";
        }
        if(parts[1].equals("true")){return parts[0];}
        if(parts[1].equals("false")){return "(not " + parts[0] + ")";}
        if(parts[1].contains("=") | parts[1].contains(">") | parts[1].contains("<")){
            Pattern pattern = Pattern.compile("(<=|>=|=|<|>)");
            Matcher matcher = pattern.matcher(parts[1]); matcher.find();
            String operator = matcher.group();
            pattern = Pattern.compile("-?\\d+(\\.\\d+)?");
            matcher = pattern.matcher(parts[1]); matcher.find();
            String value = matcher.group();
            return "(" + operator + " " + parts[0] + " " + value + ")";
        } else{
            return "(" + "=" + " " + parts[0] + " " + "\"" + parts[1]+ "\"" + ")";
        }

    }

    public static ArrayList<String> getStatementIDs(String statement) {
        ArrayList<String> result = new ArrayList<String>();
        if(!statement.contains(":")){
            result.add(statement);
            return result;
        } else{
            String[] parts = statement.split(":");
            if (parts[1].equalsIgnoreCase("true") | parts[1].equalsIgnoreCase("false")){
                result.add(parts[0]);
                return result;
            } else if (parts[1].contains("=") | parts[1].contains(">") | parts[1].contains("<")) {
                result.add(parts[0]);
                return result;
            }
            result.addAll(Arrays.asList(parts[0],parts[1]));
            return result ;
        }
    }

}