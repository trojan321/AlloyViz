/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import com.github.jabbalaci.graphviz.GraphViz;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 *
 * @author pawel
 */
public class VizualizationCreator {

    public static void createVizualization(String inputModelFilePath, Module world, String outputFileName, String outputFileType, int dpi, double ranksep, String outputPath, boolean noFuncsAndPreds) throws IOException {
        String dotFileName="temp.dot";
        
        createDotFile(inputModelFilePath, dotFileName, world, ranksep, noFuncsAndPreds);
        createOutputFile(dotFileName, outputFileName, outputFileType, dpi, outputPath, inputModelFilePath);
        
    }
    
    public static void createDotFile(String modelFilePath, String dotFileName, Module world, double ranksep, boolean noFuncsAndPreds) throws IOException {
        File file = new File(dotFileName);

        try {
            if (file.createNewFile()) {
                //System.out.println("File is created!");
            }
            else {
                //System.out.println("File already exists.");
            }
        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            System.exit(1);
            return;
        } 
        FileWriter writer=null;
        try{
            writer = new FileWriter(file);
            String toFile=createDotGraph(modelFilePath, world, ranksep, noFuncsAndPreds); 
            
            writer.write(toFile);
            writer.close();

        }
        catch (IOException e) {
            System.out.println(e.getMessage());
            if (writer!=null) writer.close(); 
            System.exit(1);
        }
    }
    public static void increaseDpi(GraphViz gv, int dpi){
        for(int i=0;i<dpi;i++) {
            gv.increaseDpi(); // (105+dpi) DPI
        }
    }
    
    static void createOutputFile(String dotFileName, String outputFileName, String outputFileType, int dpi, String outputPath, String inputModelFilePath) {
        String dir = "./";     // Linux
        String input = dir + dotFileName;
        String graphRepresentationType="dot";

        GraphViz gv = new GraphViz();
        gv.readSource(input);
        increaseDpi(gv, dpi);        
        
        File out = new File(outputPath + outputFileName + "." + outputFileType);   // Linux

        if(gv.writeGraphToFile(gv.getGraph(gv.getDotSource(), outputFileType, graphRepresentationType), out)==1) {
            String inputModelFilename=inputModelFilePath.contains("/")?inputModelFilePath.substring(inputModelFilePath.lastIndexOf("/")+1):inputModelFilePath;
            System.out.println("\n=========== Visualization for model "+inputModelFilename+" created in "+outputPath+" as "+outputFileName+"."+outputFileType+" ===========\n");
        }
        else{
            System.out.println("\n=========== There was a problem during creation of output visualization file. Please try again. ===========\n");
        }
    }
    
    static String createDotGraph (String modelFilePath, Module world, double ranksep, boolean noFuncsAndPreds) throws IOException {
        
        String fileHeader="digraph G {\n"+"rankdir=<BT>;\n"+"ranksep="+ranksep+";\n"+"nodesep="+1+";\n";
        
        ArrayList<Sig> allSigs=new ArrayList<> ();
        for(Sig sig: world.getAllSigs()) {
            allSigs.add(sig);
        }

        List<String> modelLines;
        try (BufferedReader br = Files.newBufferedReader(Paths.get(modelFilePath))) {
            modelLines = br.lines().collect(Collectors.toList());
        } 
        
        String modulesHead="";
        String modulesBody="<B> Person </B> >, fontsize=30, penwidth=5, margin=0.25][style=filled, fillcolor=gold];";
        String modulesBodyContext="";
        for (String line:modelLines){
            if(Util.testRegexPatternInText("^[ ]*open[ ]+|^[ ]*module[ ]+", line, false))
               modulesBodyContext=modulesBodyContext+line+" <BR/>"; 
        }
        if(!modulesBodyContext.isEmpty()) {
            String moduleStereotype="<B>"+Util.getLTSymbol()+Util.getLTSymbol()+"module"+Util.getGTSymbol()+Util.getGTSymbol()+"</B><BR/>";
            modulesBody="MODULES_HEAD_FORMAT_RESERVED[shape=folder,fontcolor=black, penwidth=5, color=gray45][label=< "+moduleStereotype+modulesBodyContext+" >];\n";
            modulesHead="{ rank = max; MODULES_HEAD_FORMAT_RESERVED;}\n";
        
            for (Sig sig:allSigs) {
                if(sig.isTopLevel()) {
                    modulesBody=modulesBody+"MODULES_HEAD_FORMAT_RESERVED"+"->"+SigsAndConstraintsFiller.getSigName(sig)+"[style=invis]\n";
                    break;
                }
            }
        }
        Pair<String,String> scToFile=SigsAndConstraintsFiller.fillSigsAndConstraints(allSigs,modelLines);
       
        Pair<Pair<String,String>, Pair<String,String>> ffToFile=FactsAndFuncsFiller.fillFactsAndFunctions(modelFilePath,world,allSigs,modelLines);
        Pair<String,String> factsToFile=ffToFile.a;
        Pair<String,String> funcsToFile=ffToFile.b;
        
        Pair <String,String> relToFile=RelationsFiller.fillRelations(allSigs);

        String factsHead=factsToFile.a;
        String consHead=scToFile.a;
        String relsHead=relToFile.a;
        String funcsHead=noFuncsAndPreds?"":funcsToFile.a;
        
        String fileFormatterHeader=modulesHead+factsHead+consHead+relsHead+funcsHead;
                
        String scBody=scToFile.b;
        String factsBody=factsToFile.b;
        String relsBody=relToFile.b;
        String funcsBody=noFuncsAndPreds?"":funcsToFile.b;
        
        String fileBody=modulesBody+scBody+factsBody+relsBody+funcsBody;
        
        String fileFooter="\n}\n";
        
        String toFile=fileHeader+fileFormatterHeader+fileBody+fileFooter;
        return toFile;
    }
    
}