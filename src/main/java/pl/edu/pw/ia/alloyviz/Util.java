/*
 * AlloyViz 2.0 -- Copyright (c) 2018, Paweł Masłowski, Politechnika Warszawska
 * MIT Licence
 */

package pl.edu.pw.ia.alloyviz;

import java.io.File;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 *
 * @author pawel
 */
public class Util {
    static boolean testRegexPatternInText(String pattern, String text, boolean multilineOption){
        boolean test=false;
        
        Pattern r;
        if(multilineOption)
            r=Pattern.compile(pattern,Pattern.MULTILINE);
        else
            r=Pattern.compile(pattern);
        
        Matcher m = r.matcher(text);
        
        if (m.find( ))
            test=true;
        
        return test;
    }
    
    
    static String getPatternForSeparateWord(String word){
        String sWPattern="^"+word+"$|^("+word+"\\W)|(\\W"+word+")$|(\\W"+word+"\\W)";
        return sWPattern;
    }
    
    static String getLTSymbol(){
        return "&lt;";
    }
    
    static String getGTSymbol(){
        return "&gt;";
    }
    
    /*static String transformTextIntoEscapeHtml(String text) {
        return text.replaceAll("&", "&amp;").replaceAll(">", "&gt;").replaceAll("<", "&lt;");
    }*/
    
    static boolean thereIsAlsFile(File[] listOfFiles){
        boolean test=false;
        
        for(File file:listOfFiles)
            if(file.isFile()&&file.getName().endsWith(".als"))
                test=true;
                        
        return test;
    }
    
}
