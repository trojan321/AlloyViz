/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 *
 * @author pawel
 */
public class SigsAndConstraintsFiller {
    static Pair<String,String> formOne=new Pair<String,String>(" [shape=oval]", "!");
    static Pair<String,String> formLone=new Pair<String,String>(" [shape=oval]" , "?");
    static Pair<String,String> formSome=new Pair<String,String>(" [shape=box]", "+");
    static Pair<String,String> formDefault=new Pair<String,String>(" [shape=box]","");
    
    static Pair<String,String> chooseForm(Sig sig) {
        Pair<String,String> formPhrase;
        if(sig.isOne != null){
            formPhrase=formOne;
        }
                
        else {
            if (sig.isLone != null){
                formPhrase=formLone;
            }
            
            else {
                if (sig.isSome != null){
                    formPhrase=formSome;                    
                }
                
                else {  
                    formPhrase=formDefault;
                }
            }
        }
        return formPhrase;
    }
    static String fillSigs(Sig sig) throws IOException {
        Pair<String,String> formPhrase=chooseForm(sig);
        String styleColor=sig.isSubsig!=null?"[style=filled, fillcolor=gold]":"[style=filled, fillcolor=dodgerblue1]";
        String sigName=getSigName(sig);
        boolean isAb=sig.isAbstract!=null;
        String sigsBody=sigName+formPhrase.a+styleColor+"[label=<"+" <B> "+(isAb?"<I>":"")+sigName+formPhrase.b+(isAb?"</I>":"")+" </B> "+">, fontsize=30, penwidth=5, margin=0.25];"+"\n";
        
        return sigsBody;
    }
    
    static String getSigName(Sig sig){
        String sigName=sig.toString().replaceFirst("this/", "").replace("'","PRIM");
        return sigName;
    }
    
    static String getSigName(String sig){
        String sigName=sig.replaceFirst("this/", "").replaceAll(" ", "").replace("'","PRIM");
        return sigName;
    }
    
    static Pair<String,String> fillSigsAndConstraints(List<Sig> sigs, List<String> modelLines) throws IOException {
        List<String> allConstraintsList=new ArrayList<>();
        String sigsBody="";
        String consBody="";
        String consHead="";
        for (Sig sig: sigs) {
            sigsBody=sigsBody+fillSigs(sig);
            consBody=consBody+fillConstraints(sig, allConstraintsList, modelLines);
        }
        
        if(!allConstraintsList.isEmpty()){
            consHead=consHead+"{ rank = min; ";

            for(String constraint:allConstraintsList) {
                consHead=consHead+constraint+"; ";
            }

            consHead=consHead+"}\n";
        }
        
        Pair<String,String> scToFile=new Pair<> (consHead,sigsBody+consBody);

        return scToFile;

    }
    
    static String fillConstraints(Sig sig, List<String> allConstraintsList,  List<String> modelLines) throws IOException {
        String consBody=""; 
        SafeList<Expr> constraints=sig.getFacts();
        if(constraints!=null && !constraints.isEmpty()) {
            for(int i=0;i<constraints.size();i++) {

                String constraintContext=FactsAndFuncsFiller.readFactContext(sig.getFacts().get(i), modelLines);
                String constraintName=getConstraintName(sig,i);
                String constraintStereotype="<B>&lt;&lt;constraint&gt;&gt;</B><BR/>";
                String styleColor="[style=filled, fillcolor=forestgreen]";
                consBody=consBody+constraintName+" [shape=note]"+styleColor+"[label=<"+constraintStereotype+constraintContext+">];"+"\n";
                consBody=consBody+constraintName+" -> "+getSigName(sig)+"[arrowhead=none,style=dashed];"+"\n";
                allConstraintsList.add(constraintName);
            }
        }
        return consBody;
    }
    static String getConstraintName(Sig sig, int i){
        String constraintName="Constraint"+i+"ForSig"+getSigName(sig);
        return constraintName;
    }
}
