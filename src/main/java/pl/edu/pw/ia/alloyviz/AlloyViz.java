/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package pl.edu.pw.ia.alloyviz;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import java.io.File;
import java.io.IOException;
import org.apache.commons.cli.*;

/**
 *
 * @author pawel
 */
public class AlloyViz {
    public final static double VERSION = 2.0;
    final static String DIR = System.getProperty("user.dir");
    /*
     * Execute every command in every file.
     *
     * This method parses every file, then execute every command.
     *
     * If there are syntax or type errors, it may throw
     * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
     * You should catch them and display them,
     * and they may contain filename/line/column information.
     */
    /**
     * @param args the command line arguments
     * @throws edu.mit.csail.sdg.alloy4.Err
     * @throws java.io.IOException
     */
    public static void main(String[] args) throws Err, IOException {

        // Alloy4 sends diagnostic messages and progress reports to the A4Reporter.
        // By default, the A4Reporter ignores all these events (but you can extend the A4Reporter to display the event for the user)
        A4Reporter rep = new A4Reporter() {
            // For example, here we choose to display each "warning" by printing it to System.out
            @Override public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n"+(msg.toString().trim())+"\n\n");
                System.out.flush();
            }
        };

        
        Options consoleOptions = ConsoleArgumentsConfigurator.configureOptions();
        
        // create the parser
        CommandLineParser parser = new DefaultParser();
        HelpFormatter formatter = new HelpFormatter();
        CommandLine cmd;

        try {
            // parse the command line arguments
            cmd = parser.parse(consoleOptions, args);
        } catch (ParseException e) {
            // oops, something went wrong
            System.out.println( "\n======= Parsing configuration options failed.  Reason: " + e.getMessage()+" =======\n" );
            formatter.printHelp("java -jar <path to JAR with AlloViz, i.e. AlloyViz-2.0.jar>", consoleOptions, true);

            System.exit(1);
            return;
        }

        if (cmd.hasOption("help")) {
            formatter.printHelp("java -jar <path to JAR with AlloViz, i.e. AlloyViz-2.0.jar>", consoleOptions, true);
            return;
        }
        
        if (cmd.hasOption("version")) {
            System.out.println("\n======== Version of AlloyViz: "+VERSION +" ========\n");
            return;
        }
       
        File currentJavaDir = new File(DIR).getAbsoluteFile();
        File AlloyVizHomeFolder=(currentJavaDir.getAbsolutePath().endsWith("target"))?currentJavaDir.getParentFile().getAbsoluteFile():currentJavaDir.getAbsoluteFile();
        String[] inputModelsFilePaths = cmd.getOptionValues("m");
        
        
        if (inputModelsFilePaths!=null && inputModelsFilePaths.length!=0) { 
            for(int i=0; i<inputModelsFilePaths.length; i++) {
                String inputModelFilePath=inputModelsFilePaths[i];
                File fileWithModel = new File(inputModelFilePath).getAbsoluteFile();
                
                if(!fileWithModel.exists()){
                    System.out.println("\n======= There was a problem during reading "+inputModelFilePath+" file. Probably the file doesn't exist. Please try again. =======\n");
                    System.exit(1);
                    return;
                }
                
                try {
                    parseModelAndCreateVisualization(inputModelFilePath,rep, cmd, AlloyVizHomeFolder, i);         
                }
                catch (Err e){
                    System.out.println("\n=======There was a problem during parsing the model file=======\n");
                    System.out.println(e.getMessage()+"at position "+e.pos.toShortString());
                    System.exit(1);
                    return;
                }
                catch (IOException ex){
                    System.out.println(ex.getMessage());
                    System.exit(1);
                    return;
                }
            
            }
        }
        else {
            File modelsCatalog=new File(AlloyVizHomeFolder.getAbsolutePath()+"/models/");
            File[] listOfFiles = modelsCatalog.listFiles();

            if(listOfFiles!=null && listOfFiles.length!=0 && Util.thereIsAlsFile(listOfFiles)){
                for (File file : listOfFiles) {
                    if (file.isFile() && file.getName().endsWith(".als")&&!file.getName().endsWith("integer.als")) {
                        String inputModelFilePath = modelsCatalog.getAbsolutePath()+"/"+ file.getName();
                        parseModelAndCreateVisualization(inputModelFilePath, rep, cmd, AlloyVizHomeFolder, -1);
                    }
                }
            }
            
            else {
                System.out.println("\n========= No Alloy models found. Please put at least one in models folder or use -m <model filepath> option =========\n");
            }      
        }  
    }
    
    static void parseModelAndCreateVisualization(String inputModelFilePath, A4Reporter rep, CommandLine cmd, File AlloyVizHomeFolder, int indexOfMOptionInputFiles) throws IOException, Err{
        File inputFile=new File(inputModelFilePath).getAbsoluteFile();
        System.out.println("\n=========== Parsing+Typechecking "+inputFile+" =============\n");

        Module world = CompUtil.parseEverything_fromFile(rep, null, inputModelFilePath);

        String dpiValue = cmd.getOptionValue("dpi");
        String outputFileTypeValue = cmd.getOptionValue("ot");
        String[] inputModelsFilePaths = cmd.getOptionValues("m");
        String[] outputFilenames = cmd.getOptionValues("of");
        String ranksepValue = cmd.getOptionValue("rs");
        String outputPathValue = cmd.getOptionValue("op");
        boolean outputFilenamesSetByUser=inputModelsFilePaths!=null && outputFilenames!=null && outputFilenames.length==inputModelsFilePaths.length && indexOfMOptionInputFiles!=-1;
        boolean moduleNameAsOutput=(outputFilenamesSetByUser?false:cmd.hasOption("mnao"));
        boolean noFuncsAndPreds=cmd.hasOption("nf");

        String outputFileType=(outputFileTypeValue!=null?outputFileTypeValue:"png");
        int dpi=(dpiValue!=null?Integer.parseInt(dpiValue)-105:8); //105+dpi DPI (155 DPI)
        double ranksep=(ranksepValue!=null?Double.parseDouble(ranksepValue):1.5);
        File visualizationsCatalog=new File(AlloyVizHomeFolder.getAbsolutePath()+"/visualizations/");
        File outputDir;
        String outputPath=visualizationsCatalog.getAbsolutePath()+"/";
        if(outputPathValue!=null){
            outputDir=new File(outputPathValue);
            if(outputDir.exists()&&outputDir.isDirectory())
                outputPath=outputDir.getAbsolutePath()+"/";
        }
        String moduleName=world.getModelName();
        String simplifiedModuleName=moduleName.contains("/")?moduleName.split("/")[moduleName.split("/").length-1]:moduleName;
        String modelFileName=inputModelFilePath.contains("/")?inputModelFilePath.split("/")[inputModelFilePath.split("/").length-1]:inputModelFilePath;
        String simplifiedModelName=modelFileName.contains(".")?modelFileName.substring(0, modelFileName.lastIndexOf(".")):modelFileName;
        String outputFileName=outputFilenamesSetByUser?outputFilenames[indexOfMOptionInputFiles]:moduleNameAsOutput?simplifiedModuleName:simplifiedModelName;

        VizualizationCreator.createVizualization(inputModelFilePath, world, outputFileName, outputFileType, dpi, ranksep, outputPath, noFuncsAndPreds);

    }
   
}