

/*
 * This class : a pour objectif de tester la simulation de fichier de l'intervention creer par loubna
 * add le 15 avril 2024 
 */

 package forceps.myscripts.loubna;
import java.util.List;


import jeeb.lib.util.Record;
import jeeb.lib.util.fileloader.FileLoader;

/**
 * Another simulation command file reader, for loubna TALEB 
 * 
 * @author loubna TALEB 2024
 */
public class SimulationloubnaCommadReader extends FileLoader  {
    public String setupFileName;
    public int numberOfYearsToBeJumped;
    public int exportTimeStep;
    public List<SimulationLine> simulationLines;
    /*Constructeur
     */
    public SimulationloubnaCommadReader() throws Exception {
        super ();
    }
    protected void checks() throws Exception {
 
		// checkAssertion throws an exception if trouble
		
		checkAssertion(numberOfYearsToBeJumped >= 0, "numberOfYearsToBeJumped must be >= 0");
		checkAssertion(exportTimeStep >= 1, "exportTimeStep must be >= 1");
		checkAssertion(simulationLines != null && !simulationLines.isEmpty (), "At least one simulation line must be provided");

 
	}
    static public class SimulationLine extends Record {
 
		public String siteFileName;
		public String climateFileName;
		public String inventoryFileName; 
		public String potentialSpeciesList;
		public String scenario;

		public SimulationLine(String line) throws Exception {
			super(line);
		}
	}

    
}
