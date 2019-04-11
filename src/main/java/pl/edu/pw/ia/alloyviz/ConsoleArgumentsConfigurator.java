/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionBuilder;
import org.apache.commons.cli.Options;

/**
 *
 * @author pawel
 */
public class ConsoleArgumentsConfigurator {
    public static Options configureOptions () {
        
        Options consoleOptions = new Options();

        Option dpiOpt = new Option("dpi", true, "output file dpi");
        dpiOpt.setRequired(false);
        consoleOptions.addOption(dpiOpt);
        
        consoleOptions.addOption(OptionBuilder.withLongOpt("m")
        .withDescription("paths to sources of input models")
        .hasArgs()
        .create());
    
        consoleOptions.addOption("mnao", false, "set output files' names from module names"); //ModuleNameAsOutput
        
        Option outputTypeOpt = new Option("ot", true, "output file type");
        outputTypeOpt.setRequired(false);
        consoleOptions.addOption(outputTypeOpt);
        
        Option outputPathOpt = new Option("op", true, "output path for results");
        outputPathOpt.setRequired(false);
        consoleOptions.addOption(outputPathOpt);
                
        consoleOptions.addOption(OptionBuilder.withLongOpt("on")
        .withDescription("filenames for output visualizations")
        .hasArgs()
        .create());
        
        consoleOptions.addOption("nc", false, "generate visualizations in black-white colors");
        
        Option help = new Option( "help", "print this message" );
        
        Option version = new Option( "version", "print the version information and exit" );
        
        consoleOptions.addOption( help );

        consoleOptions.addOption( version );
        
        return consoleOptions;
    }
}
