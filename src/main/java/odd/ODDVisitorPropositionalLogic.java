package odd;

import org.antlr.v4.runtime.tree.ParseTree;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ODDVisitorPropositionalLogic extends ODDBaseVisitor<String> {

    private final LinkedHashMap<String, String> modulesHashmap = new LinkedHashMap<String, String>();
    private String result, moduleName, currentStatement = "";

    @Override
    public String visitInput(ODDParser.InputContext ctx) {
        String output = "";

        for (int i = 0; i < ctx.getChildCount(); i++) {
            ParseTree child = ctx.getChild(i);
            child.accept(this);
        }

        String between = modulesHashmap.size() > 1 ? "\n\n" : "";
        Iterator<Map.Entry<String, String>> it = modulesHashmap.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<String, String> entry = it.next();
            output += entry.getKey() + ":=\n" + entry.getValue();
            if (it.hasNext()) {
                output += between;
            }
        }

        return output;
    }


    @Override
    public String visitModule(ODDParser.ModuleContext ctx) {
        result = "";
        moduleName ="";
        if(ctx.statement() != null){moduleName=ctx.statement().ID().getText().replace(":","");
        result = visitChildren(ctx);}
        else {
            moduleName = ctx.getChild(0).getText().replace(":", "");
            visitChildren(ctx);
        }
        return modulesHashmap.put(moduleName,"[" + result + "]");
    }

    @Override
    public String visitInclude_and(ODDParser.Include_andContext ctx) {

        int childCount = ctx.getChildCount();
        String include_and = childCount>2?"(":"";

        for (int i = 1; i < childCount; i++) {

            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
                if (i != ctx.getChildCount() - 1) {
                    child.accept(this);
                    include_and += currentStatement + " & ";
                }else{
                    child.accept(this);
                    include_and += childCount>2?currentStatement + ")": currentStatement;

                }
            }
        if (result.isEmpty()) {
            return result += include_and;
        } else {
            return result += " & " + include_and;
        }
    }

    @Override
    public String visitInclude_or(ODDParser.Include_orContext ctx) {

        int childCount = ctx.getChildCount();
        String include_or = childCount>2?"(":"";

        for (int i = 1; i < childCount; i++) {

            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
            if (i != ctx.getChildCount() - 1) {
                child.accept(this);
                include_or += currentStatement + " | ";
            }else{
                child.accept(this);
                include_or += childCount>2?currentStatement + ")": currentStatement;

            }
        }
        if (result.isEmpty()) {
            return result += include_or;
        } else {
            return result += " & " + include_or;
        }
    }

    @Override
    public String visitExclude_and(ODDParser.Exclude_andContext ctx) {
        int childCount = ctx.getChildCount();
        String exclude_or = childCount>2?"(!(":"(!";
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
            if (i != ctx.getChildCount() - 1) {
                child.accept(this);
                exclude_or += currentStatement + " & ";
            }else{
                child.accept(this);
                exclude_or +=childCount>2?currentStatement + "))":currentStatement + ")";

            }
        }
        if (result.isEmpty()) {
            return result += exclude_or;
        } else {
            return result += " & " + exclude_or;
        }
    }

    @Override
    public String visitExclude_or(ODDParser.Exclude_orContext ctx) {
        int childCount = ctx.getChildCount();
        String exclude_or = childCount>2?"(!(":"(!";
        for (int i = 1; i < childCount; i++) {
            org.antlr.v4.runtime.tree.ParseTree child = ctx.getChild(i);
                if (i != ctx.getChildCount() - 1) {
                    child.accept(this);
                    exclude_or += currentStatement + " | ";
                }else{
                    child.accept(this);
                    exclude_or +=childCount>2?currentStatement + "))":currentStatement + ")";

                }
            }
        if (result.isEmpty()) {
            return result += exclude_or;
        } else {
            return result += " & " + exclude_or;
        }
    }

    @Override
    public String visitStatement(ODDParser.StatementContext ctx) {

        int childCount = ctx.getChildCount();
        currentStatement = childCount>2?"(":"";
        boolean statementID0inHashmap = false;
        boolean statementID1inHashmap = false;
        if (ctx.getChildCount() ==1){
            if(modulesHashmap.get(ctx.getText()) != null) {
                return currentStatement += modulesHashmap.get(ctx.getText());
            }
            return currentStatement += translateStatementToPropositionalLogic(ctx.getText());
        }
        for (int i = 1; i < ctx.getChildCount(); i++) {
            org.antlr.v4.runtime.tree.ParseTree child0 = ctx.getChild(0);
            org.antlr.v4.runtime.tree.ParseTree childI = ctx.getChild(i);
            String statement = child0.getText() + childI.getText();
            ArrayList<String> statementIDs = getStatementIDs(statement);
            if(statementIDs.size() ==2) {
                statementID0inHashmap = modulesHashmap.get(statementIDs.get(0)) != null;
                statementID1inHashmap = modulesHashmap.get(statementIDs.get(1)) != null;
                if (statementID0inHashmap && statementID1inHashmap) {
                    if (i != childCount - 1) {
                        currentStatement += translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0)) + ":" + modulesHashmap.get(statementIDs.get(1))) + " | ";
                    } else {
                        currentStatement += childCount > 2 ? translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0)) + ":" + modulesHashmap.get(statementIDs.get(1))) + ")"
                                : translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0)) + ":" + modulesHashmap.get(statementIDs.get(1)));
                    }
                }
                if (statementID0inHashmap && !statementID1inHashmap) {
                    if (i != childCount - 1) {
                        currentStatement += translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+statementIDs.get(1)) + " | ";
                    } else {
                        currentStatement += childCount > 2 ? translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+statementIDs.get(1)) + ")"
                                : translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+statementIDs.get(1));
                    }
                }
                if (!statementID0inHashmap && statementID1inHashmap) {
                    if (i != childCount - 1) {
                        currentStatement += translateStatementToPropositionalLogic(statementIDs.get(0)+":"+modulesHashmap.get(statementIDs.get(1))) + " | ";
                    } else {
                        currentStatement += childCount > 2 ? translateStatementToPropositionalLogic(statementIDs.get(0)+":"+modulesHashmap.get(statementIDs.get(1))) + ")"
                                : translateStatementToPropositionalLogic(statementIDs.get(0)+":"+modulesHashmap.get(statementIDs.get(1)));
                    }
                }
            }
            if (modulesHashmap.get(statementIDs.get(0)) != null) {
                if (i != childCount - 1) {
                    currentStatement += translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+childI.getText()) + " | ";
                } else {
                    currentStatement += childCount > 2 ? translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+childI.getText()) + ")"
                            : translateStatementToPropositionalLogic(modulesHashmap.get(statementIDs.get(0))+":"+childI.getText());
                }
            }
                else {
                    if (i != ctx.getChildCount() - 1) {
                        currentStatement += translateStatementToPropositionalLogic(statement) + " | ";
                    } else {
                        currentStatement +=childCount>2?translateStatementToPropositionalLogic(statement) + ")":translateStatementToPropositionalLogic(statement);
                    }
                }
            }

        return currentStatement;
    }
    public static String translateStatementToPropositionalLogic(String statement) {
        if(!statement.contains(":")){
            return statement;
        }
        String[] parts = statement.split(":");
        if(parts[1].equals("true")){return parts[0];}
        if(parts[1].equals("false")){return "(!" + parts[0] + ")";}
        if(parts[1].contains("=") | parts[1].contains(">") | parts[1].contains("<")){
            Pattern pattern = Pattern.compile("(<=|>=|=|<|>)");
            Matcher matcher = pattern.matcher(parts[1]); matcher.find();
            String operator = matcher.group();
            pattern = Pattern.compile("-?\\d+(\\.\\d+)?");
            matcher = pattern.matcher(parts[1]); matcher.find();
            String value = matcher.group();
            return "(" + parts[0] + " " + operator + " " + value + ")";
        } else{
            return "(" + parts[0] + " " + "=" + " " + parts[1] + ")";
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

    public LinkedHashMap<String, String> getModulesHashmap() {
        return modulesHashmap;
    }

}