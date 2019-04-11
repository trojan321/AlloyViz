/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import org.apache.commons.lang.StringUtils;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 *
 * @author pawel
 */
public class FactsAndFuncsFiller {
    
    static String getUnifiedFactName(Pair<String, Expr> fact){
        String factName=fact.a;
        
        if (factName.contains("$"))
            factName=factName.replaceFirst("\\$", "");
        else
            factName="fact"+factName;
        
        return factName;
    }
     
    static Set<Sig> findSigsRelatedToFact(Pair<String,Expr> fact, List<Sig> allSigs, List<String> modelLines) throws IOException {
        Set<Sig> sigsRelatedToFact=new HashSet<>();
        
        for (Sig sig:allSigs){
            if(isSigRelatedToFact(sig, fact, modelLines))
                sigsRelatedToFact.add(sig);
        }
        
        return sigsRelatedToFact;
    }
    
    static boolean factContextContainsSig(String factContext, Sig sig) {
        boolean contains=false;
             
        String sigName=SigsAndConstraintsFiller.getSigName(sig);
        String pattern = Util.getPatternForSeparateWord(sigName);

        if(Util.testRegexPatternInText(pattern, factContext, true))
           contains=true;
        
        return contains;
    }
            
    static boolean isSigRelatedToFact(Sig sig, Pair<String,Expr> fact, List<String> modelLines) throws IOException {
        boolean isSigRelatedToFact=false;
        

        String factContext=readFactContext(fact.b, modelLines);
        
        if (factContextContainsSig(factContext, sig)){
            isSigRelatedToFact=true;
        }
        
        return isSigRelatedToFact;
    }
    static Pair<String,String> fillFacts(Module world, List<Sig> allSigs, List<String> modelLines, SafeList<Pair<String,Expr>> factsList) throws IOException {
        String factHead="";
        String factBody="";
     
        if (factsList!=null && !factsList.isEmpty()) {
            
            factHead=factHead+"{ rank = min; ";
            
            for(Pair<String,Expr> fact:factsList) {
                String unifiedFactName=getUnifiedFactName(fact);
                factHead=factHead+unifiedFactName+"; ";
            }
            factHead=factHead+"}\n";
            
            
            
            
            
            for(Pair<String,Expr> fact:factsList) {

                String factContext=readFactContext(fact.b, modelLines);
                boolean isUnnamedFact=fact.a.contains("$");
                String unifiedFactName=getUnifiedFactName(fact);
                String factStereotype=getFactStereotype(unifiedFactName,isUnnamedFact);
                String styleColor="[style=filled,fillcolor=darkgreen,fontcolor=white]";
                factBody=factBody+unifiedFactName+" [shape=note] "+styleColor+"[label=<"+factStereotype+factContext+">];"+"\n";
            }
            
            
            for(Pair<String,Expr> fact:factsList) {
                String unifiedFactName=getUnifiedFactName(fact);
                Set<Sig> relatedSigsToFact=findSigsRelatedToFact(fact,allSigs,modelLines);
                for(Sig relSig:relatedSigsToFact){
                    factBody=factBody+unifiedFactName+" -> "+SigsAndConstraintsFiller.getSigName(relSig)+"[arrowhead=none,style=dashed];\n";
                }
            }
            
            
            
            
            
        }
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        Pair<String,String> factsToFile=new Pair<>(factHead,factBody);
        return factsToFile;
    }
    
    static String getFactStereotype(String factName, boolean unnamedFact){    
        factName=factName.replaceFirst("fact", "");
        String factStereoType=unnamedFact?" <B> "+"&lt;&lt;fact&gt;&gt;"+" </B> <BR/> ":" <B> &lt;&lt;fact&gt;&gt; </B> <BR/> <U> "+factName+" </U> <BR/> ";
        return factStereoType;
    }
    
    static Set<Func> findRelevantFuncs (SafeList<Pair<String,Expr>> factsList, SafeList<Func> funcsList) {
        Set<Func> relevantFuncs = new HashSet<>();
        
        for (Pair<String,Expr> fact:factsList){
            for(Func func:fact.b.findAllFunctions()){
                if(funcsList.contains(func))
                        relevantFuncs.add(func);
            }
        }
        
        return relevantFuncs;
    }
    
    static Pair<String,String> fillFuncs(Module world, List<String> modelLines, SafeList<Pair<String,Expr>> factsList) throws IOException {
        String funcsHead;
        String funcsBody;
        String onlyFunsHead="";
        String onlyFunsBody="";
        String onlyPredsHead="";
        String onlyPredsBody="";
        SafeList<Func> funcsList=world.getAllFunc();
        
        Set<Func> relevantFuncsSet=findRelevantFuncs(factsList, funcsList);
        
        List<Func> onlyFunsList=new ArrayList<> ();
        List<Func> onlyPredsList=new ArrayList<> ();

        if (!relevantFuncsSet.isEmpty()) {
            
            relevantFuncsSet.forEach((relevantFunc) -> {
                if(relevantFunc.isPred)
                    onlyPredsList.add(relevantFunc);
                else
                    onlyFunsList.add(relevantFunc);
            });
        }
        
        if (!onlyFunsList.isEmpty()) {
            onlyFunsHead=onlyFunsHead+"{ rank = same; ";
            for(Func fun:onlyFunsList) {
                String funName=getSimplifiedFunctionName(fun);
                onlyFunsHead=onlyFunsHead+funName+"; ";
            }
            onlyFunsHead=onlyFunsHead+"}\n";
        }
        
        if (!onlyPredsList.isEmpty()) {
            onlyPredsHead=onlyPredsHead+"{ rank = same; ";
            for(Func pred:onlyPredsList) {
                String predName=getSimplifiedFunctionName(pred);
                onlyPredsHead=onlyPredsHead+predName+"; ";
            }
            onlyPredsHead=onlyPredsHead+"}\n";
        }

        funcsHead=onlyFunsHead+onlyPredsHead;
        
        
        for(Func fun:onlyFunsList) {
                Pos pos=fun.pos();
                String funName=readFunctionName(pos, modelLines);
                String funContext=readFunctionContext(fun,modelLines);
                String simplifiedFunName=getSimplifiedFunctionName(fun);
                String funcStereotype="<B>&lt;&lt;fun&gt;&gt;</B><BR/>";
                String styleColor="[style=filled, fillcolor=lightgrey]";
                onlyFunsBody=onlyFunsBody+simplifiedFunName+" [shape=note] "+styleColor+"[label=<"+funcStereotype+funName+"<BR/>"+funContext+">];"+"\n";
            }
        
        for(Func pred:onlyPredsList) {
                Pos pos=pred.pos();
                String predName=readFunctionName(pos, modelLines);
                String predContext=readFunctionContext(pred,modelLines);
                String simplifiedPredicateName=getSimplifiedFunctionName(pred);
                String predStereotype="<B>&lt;&lt;pred&gt;&gt;</B><BR/>";
                String styleColor="[style=filled, fillcolor=gray]";
                onlyPredsBody=onlyPredsBody+simplifiedPredicateName+" [shape=note] "+styleColor+"[label=<"+predStereotype+predName+"<BR/>"+predContext+">];"+"\n";
            }
             
        funcsBody=onlyFunsBody+onlyPredsBody;
        
        Pair<String,String> funToFile=new Pair<>(funcsHead,funcsBody);
        return funToFile;
    }
    static Pair<Pair<String,String>, Pair<String,String>> fillFactsAndFunctions(String modelFilePath, Module world, List<Sig> sigs, List<String> modelLines) throws IOException {
       
        SafeList<Pair<String,Expr>> factsList=world.getAllFacts();

        Pair<String,String> factToFile = fillFacts(world, sigs, modelLines, factsList);
        Pair<String,String> funToFile = fillFuncs(world, modelLines, factsList);
        
        Pair<Pair<String,String>, Pair<String,String>> ffToFile = new Pair <> (factToFile,funToFile);
        
        return ffToFile;
       
    }
    
    
    
    static String readFactContext(Expr fact, List<String> lines) throws IOException {
        Pos pos=fact.pos();
        String factContext=readContext(pos,lines);
        return factContext;
    }
    
    
    static String readFunctionContext(Func func, List<String> lines) throws IOException {
        Pos pos=func.pos();
        
        String funcContext=readContext(pos,lines);
        return funcContext;
    }
      
    static String readFunctionName(Pos pos, List<String> lines) throws IOException {
        String name="";
        
        int lineNr_B=pos.y-1;
        int lineNr_E=pos.y2-1;
        int columnNr;
        String line;
        
        for (int i=lineNr_B; i<=lineNr_E && i<lines.size(); i++) {
            String toAdd;
            line=lines.get(i);
            if (line.contains("{")){
                columnNr=line.indexOf("{");   
                toAdd=line.substring(0,columnNr);
                name=name+toAdd;
                break;
            }
            else {
                toAdd=line;
                name=name+toAdd;
            }
        }
        return transformTextIntoEscapeHtml(name);
    }

    static String readContext(Pos pos, List<String> lines) throws IOException {

        String context="";

        if (lines!=null && !lines.isEmpty()) {     

            int lineNr_B=pos.y-1;
            int lineNr_E=pos.y2-1;
            int columnNr_E=lines.get(lineNr_E).lastIndexOf("}");               

            String line;
            int actualLineNr_B=lineNr_B;
            int columnNr_B=0;
            for (int i=lineNr_B; i<=lineNr_E && i<lines.size(); i++) {
                line=lines.get(i);
                if (line.contains("{")){
                    if (line.equals("{") || (line.endsWith("{") && StringUtils.countMatches(line,"{")==1)) {
                        actualLineNr_B=i+1;
                        break;
                    }
                    else {
                        columnNr_B=line.lastIndexOf("{")+1;
                        actualLineNr_B=i;
                        break;
                    }
                    
                }
            }
         
            for (int j=actualLineNr_B; j<=lineNr_E && j<lines.size(); j++) {
                String toAdd;
                line=lines.get(j);
                
                if(actualLineNr_B==lineNr_E) {
                    toAdd=line.substring(columnNr_B, columnNr_E);                                     
                }
                else {
                    if(j==actualLineNr_B) 
                        toAdd=line.substring(columnNr_B);
                    else {
                        if(j==lineNr_E)
                            toAdd=line.substring(0, columnNr_E);                   
                        else 
                            toAdd=line;
                    }
                }
                
            context=context+"<BR/>"+toAdd;
            }
       
        }
        
        return transformTextIntoEscapeHtml(context);
    }
    
    static String transformTextIntoEscapeHtml(String text) {
        return text.replace("<BR/>", ":-:-:-:-:").replace("&", "&amp;").replace(">", "&gt;").replace("<", "&lt;").replace("//", "\"/\"/").replace(":-:-:-:-:","<BR/>");
    }
    
    static String getSimplifiedFunctionName(Func func) {
        Pos pos=func.pos();
        int lineNr_B=pos.y-1;
        int lineNr_E=pos.y2-1;
        int columnNr_B=pos.x;
        int columnNr_E=pos.x2;
    
        String simplifiedFunctionName="Fun"+lineNr_B+lineNr_E+columnNr_B+columnNr_E;
        return simplifiedFunctionName;
    }
        
}
