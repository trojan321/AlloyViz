/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import com.github.kentliau.tree.TreeNode;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.apache.commons.lang.StringUtils;

/**
 *
 * @author pawel
 */
public class RelationsFiller {
    
    static Pair <String,String> fillRelations(List<Sig> allSigs){
        
        String relsHead="";
        
        Pair<List<String>, String> loneSigsAndRelsBody=getLoneSigsAndRelsBody(allSigs);
       
        String relsBody=loneSigsAndRelsBody.b;

        List<String> loneSigsNames=loneSigsAndRelsBody.a;
        if(loneSigsNames!=null && !loneSigsNames.isEmpty()) {
            relsHead=relsHead+"{ rank = max; ";
            
            for(String loneSigName:loneSigsNames) {
                relsHead=relsHead+loneSigName+"; ";
            }
            relsHead=relsHead+"}\n";
        }
                
        Pair <String,String> relToFile = new Pair<>(relsHead,relsBody);
        return relToFile;
    }
    
    static Pair<List<String>, String> getLoneSigsAndRelsBody(List<Sig> allSigs){
        
        List<String> loneSigs=new ArrayList<>();
        
        allSigs.forEach((sig) -> {
            loneSigs.add(SigsAndConstraintsFiller.getSigName(sig));
        });
        
        String fRelsBody=getFieldRelationsBody(allSigs, loneSigs);
        String hRelsBody=fillHierarchyRelationsBody(allSigs,loneSigs);
        String relsBody=hRelsBody+fRelsBody;
                
        Pair<List<String>, String> loneSigsAndRelsBodyPair = new Pair<>(loneSigs,relsBody);
        return loneSigsAndRelsBodyPair;
    }
    
    static int countFieldRelationArity(Decl fDecl){
        int arity=StringUtils.countMatches(fDecl.expr.toString(), "->")+2;

        return arity;
    }
    
    static String fillFieldRelation(Decl fDecl, List<Sig> allSigs, List<String> loneSigs) {
        List<Pair<String,String>> fieldRelationParts = findFieldRelationParts(fDecl,allSigs);
        
        String fieldRelation=fillFieldRelationContext(fieldRelationParts,loneSigs);
     
        return fieldRelation;
    }
   
    static String getMultiplicitySymbol(String multKeyword,int arity){
        String multiplicitySymbol=multKeyword.equals("one")?"!":multKeyword.equals("lone")?"?":multKeyword.equals("some")?"+":multKeyword.equals("set")?"set":"";
        if(arity==2&&multiplicitySymbol.isEmpty())
            multiplicitySymbol="!";
        if(multiplicitySymbol.equals("set"))
            multiplicitySymbol="";
        
        return multiplicitySymbol;
    }
    
    static String fillFieldRelationContext (List<Pair<String,String>> fieldRelationParts,List<String> loneSigs){
        int arity=fieldRelationParts.size();
        String relationName=fieldRelationParts.get(0).b;
        String fieldRelationContext="";
        String styleColor="[style = filled, color = orange]";
        if(arity==2){
            String multiplicitySymbol=getMultiplicitySymbol(fieldRelationParts.get(1).b,arity);
            fieldRelationContext=fieldRelationContext+fieldRelationParts.get(0).a+" -> "+fieldRelationParts.get(1).a+styleColor+"[label=<<B>"+relationName+multiplicitySymbol+"</B>"+">"+", arrowsize=1, fontsize=21, penwidth=3]"+";\n";
            loneSigs.remove(fieldRelationParts.get(0).a);
            loneSigs.remove(fieldRelationParts.get(1).a);
        }
            else {
                fieldRelationContext=fieldRelationContext+fieldRelationParts.get(0).a+" -> "+fieldRelationParts.get(arity-1).a+styleColor+"[label=<<B>"+relationName;
                
                for (int j=1;j<arity-1;j++)
                    fieldRelationContext=fieldRelationContext+"."+Util.getLTSymbol()+fieldRelationParts.get(j).a+Util.getGTSymbol();
                
                fieldRelationContext=fieldRelationContext+"</B>"+">"+", arrowsize=1, fontsize=21, penwidth=3]"+";\n";   
                loneSigs.remove(fieldRelationParts.get(0).a);
                loneSigs.remove(fieldRelationParts.get(arity-1).a);
            } 
        
        return fieldRelationContext;
    }
    
    static List<Pair<String,String>> findFieldRelationParts(Decl fDecl, List<Sig> allSigs){
        List<Pair<String,String>> fieldRelationParts=new ArrayList<>();
       
        String firstPart=StringUtils.substringBetween(fDecl.names.toString(), "(", ")");
        String firstPartSigName=SigsAndConstraintsFiller.getSigName(firstPart.split("<:")[0].replace(" ", ""));
        String firstPartRelationName=firstPart.split("<:")[1].replace(" ", "");
        Pair<String,String> firstPair=new Pair<>(firstPartSigName,firstPartRelationName);
        fieldRelationParts.add(firstPair);
      
        List<Pair<String,String>> anotherPairs=splitFRExprToSigMultPairs(fDecl,allSigs);
        fieldRelationParts.addAll(anotherPairs);
        
        return fieldRelationParts;
    }
   
    static List<Pair<String,String>> splitFRExprToSigMultPairs(Decl fDecl, List<Sig> allSigs){
        List<Pair<String,String>> sigMultPairs = new ArrayList<>();
        List<String> relationParts=new ArrayList<>();
        String expr=fDecl.expr.toString();
        int arity=countFieldRelationArity(fDecl);
        
        if(arity>2){
            String[] splitedParts=expr.split("->");
            relationParts.addAll(Arrays.asList(splitedParts));
        }
        else {
            relationParts.add(expr);
        }
        
        relationParts.stream().map((fRPart) -> splitFRExprPartToSigMultPair(fRPart,allSigs,arity)).forEachOrdered((pair) -> {
            sigMultPairs.add(pair);
        });
        
        return sigMultPairs;
    }
   
    static String getFRPartMultiplicity(String fRPart){
        String multiplicity="";
        List<String> multiplicitiesKeywords = Arrays.asList("one", "lone", "set", "some");

        for(String multiplicityKeyword:multiplicitiesKeywords){
            if(Util.testRegexPatternInText(multiplicityKeyword, fRPart, false)){
                multiplicity=multiplicityKeyword;
                break;
            }
        }
        
        return multiplicity;
    }
    
    static String findFRPartSig(String fRPart, List<Sig> allSigs){
        String sigName="";
        for(Sig sig:allSigs){
            if(Util.testRegexPatternInText(SigsAndConstraintsFiller.getSigName(sig), fRPart, false)){
                sigName=SigsAndConstraintsFiller.getSigName(sig);
                break;
            }
        }
        return sigName;
    }
    static Pair<String,String> splitFRExprPartToSigMultPair(String fRPart, List<Sig> allSigs, int relationArity){
        Pair<String,String> sigMultPair;  
     
        String sig=findFRPartSig(fRPart,allSigs);
                
        String multipicity=getFRPartMultiplicity(fRPart);
        
        sigMultPair=new Pair<>(sig,multipicity);
       
        return sigMultPair;
    }
    static String getFieldRelationsBody(List<Sig> allSigs, List<String> loneSigs){
        String fRelsBody="";
        for(Sig sig:allSigs){
            for(Decl fDecl:sig.getFieldDecls()){
                String fRelation=fillFieldRelation(fDecl,allSigs,loneSigs);
                fRelsBody=fRelsBody+fRelation;
            }
        }              
        
        return fRelsBody;
    }
    
    static String fillHierarchyRelationsBody(List<Sig> allSigs, List<String> loneSigs){
        
        TreeNode<Pair<String,String>> root = new TreeNode<>(new Pair<>("artificialRootOfAllSigsWithoutName","artificialRootOfAllSigs"));
        List<Sig> topLevelSigs=new ArrayList<>();
        List<Sig> nonTopLevelSigs=new ArrayList<>();
        
        allSigs.forEach((sig) -> {
            if(sig.isTopLevel()) {
                topLevelSigs.add(sig);
            }
            else {
                nonTopLevelSigs.add(sig);
            }
        });
        
        topLevelSigs.forEach((tlSig) -> {
            TreeNode<Pair<String,String>> topLevelNode=root.addChild(new Pair<> (SigsAndConstraintsFiller.getSigName(tlSig),"topLevelSig"));
            fillChildrenInTree(topLevelNode,tlSig,nonTopLevelSigs);
        });        
        

        String hRelsBody=getHRelsFromTree(root,loneSigs);
                  
        return hRelsBody;
    }

    static String getHRelsFromTree(TreeNode<Pair<String,String>> node,List<String> loneSigs){
        String hRels="";
        String styleColor="[arrowhead=<empty>,arrowsize=2.4,penwidth=3][color=navyblue]";
        List<TreeNode<Pair<String,String>>> children=node.children;
        for(TreeNode<Pair<String,String>> child:children) {
            if(child.data.b.equals("in")){
                hRels=hRels+child.data.a+" -> "+node.data.a+styleColor+"[label=<<B>in</B>>,fontsize=22];\n";
                loneSigs.remove(child.data.a);
                loneSigs.remove(node.data.a);                
            }
            if(child.data.b.equals("extends")) {
                hRels=hRels+child.data.a+" -> "+node.data.a+styleColor+";\n";
                loneSigs.remove(child.data.a);
                loneSigs.remove(node.data.a);
            }
            hRels=hRels+getHRelsFromTree(child,loneSigs);
        }
        return hRels;
    }
    
    static void fillChildrenInTree(TreeNode<Pair<String,String>> node, Sig sig, List<Sig> nonTopLevelSigs) {
        List<Pair<Sig,String>> children = findChildren(nonTopLevelSigs,sig);

        children.forEach((child) -> {
            Pair<String,String> childInUniForm=new Pair(SigsAndConstraintsFiller.getSigName(child.a),child.b);
            TreeNode<Pair<String,String>> childNode=node.addChild(childInUniForm);
            fillChildrenInTree(childNode,child.a,nonTopLevelSigs);
            });

    }   
    
    static List<Pair<Sig,String>> findChildren(List<Sig> nonTopLevelSigs, Sig parent) {
        List<Pair<Sig,String>> children = new ArrayList<>();
        List<Sig> descendents=new ArrayList<>();
       
        nonTopLevelSigs.stream().filter((sig) -> (sig.isSameOrDescendentOf(parent)&&!sig.isSame(parent))).forEachOrdered((sig) -> {
            descendents.add(sig);
        });
        
        descendents.forEach((sigDes1) -> {
            int counter=0;
            counter = descendents.stream().filter((sigDes2) -> (sigDes1.isSameOrDescendentOf(sigDes2)&&!sigDes1.isSame(sigDes2))).map((_item) -> 1).reduce(counter, Integer::sum);
            if (counter==0) {
                if (sigDes1.isSubset!=null) {
                    Pair<Sig,String> pair=new Pair<>(sigDes1,"in");
                    children.add(pair);
                }
                else {
                    Pair<Sig,String> pair=new Pair<>(sigDes1,"extends");
                    children.add(pair);                       
                }
            }
        });
        
        return children;
    }
            
  
}
