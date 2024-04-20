/*
 * The Forceps model.
 *
 * Copyright (C) April 2013: X. Morin (CNRS CEFE).
 *
 * This file is part of the Forceps model and is NOT free software. It is the property of its
 * authors and must not be copied without their permission. It can be shared by the modellers of the
 * Capsis co-development community in agreement with the Capsis charter
 * (http://capsis.cirad.fr/capsis/charter). See the license.txt file in the Capsis installation
 * directory for further information about licenses in Capsis.
 */

 package forceps.extension.intervener;

 import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
 import java.io.IOException;
 import java.util.ArrayList;
 import java.util.Collection;
 import java.util.Collections;
 import java.util.HashMap;
 import java.util.HashSet;
 import java.util.Iterator;
 import java.util.List;
 import java.util.Map;
 import java.util.Random;
 import java.util.Set;
 import java.util.StringTokenizer;

import javax.rmi.ssl.SslRMIClientSocketFactory;

import capsis.defaulttype.Tree;
 import capsis.defaulttype.TreeList;
 import capsis.kernel.GModel;
 import capsis.kernel.GScene;
 import capsis.kernel.Step;
 import capsis.kernel.extensiontype.AbstractGroupableIntervener;
 import capsis.kernel.extensiontype.Intervener;
 import capsis.util.group.GroupableIntervener;
 import capsis.util.group.GroupableType;
 import forceps.model.CepsInitialParameters;
 import forceps.model.CepsModel;
 import forceps.model.CepsScene;
 import forceps.model.CepsTree;
 import jeeb.lib.util.AdditionMap;
 import jeeb.lib.util.Alert;
 import jeeb.lib.util.AmapTools;
 import jeeb.lib.util.Log;
 import jeeb.lib.util.Translator;
 
 /**
  * CepsGHAThinnerComposition:est une autre façon pour couper dans l'ordre croissant de score alpha
  * qui depend de type d'ecalirci {0,1,0.5} tout en minimisant l'écart entre la composition cible et 
  * actuelle pour inclure ceci en algo genetiques 
  * la composition est choisis dans l'intervale {0,10,20....90,100} pour reduire les combinaisons possibles pour 5 especes
  * dans un genome (itenéraire sylvicole ) avec 5 especes on a 890 combinaisons possibles et dont la somme est egale à 100
  *on a choisis cette composition pour etre plus rapide et plus efficace dans l'exploration de l'espace 
  * des controles viables (crossover et mutation )
  *c'est pour cette raison ,j'ai adopter une façon de coupe tout en respectant les autres contraintes de coupe:
  * Respecter la surface terrière objective 
  *Respecter le type d'eclairci : croissant -décroissant -aléatoire
  *essayer de minimiser l'ecart entre la composition cible et actuelle tout en respectant que la surface 
  *terriere actuelle *100/G_% >= G_objt
  *Demontsration : à la fin on veut que G_cible =(peu pres) G_rest_actuelle 
  *donc on a : G_cible =C_cible*Gobj/100 
  *mais il faut  que G_rest_actuelle>G_cible =C_cible*Gobj/100 
  *donc il faut choisir le min telque k est l'arbre qui minimise cette ecart à chaque coupe  et qui respecte aussi
  *G_rest_actuelle_k>G_cible =C_cible*Gobj/100 (s'il respecte pas on la coupe pas mais on le choisis pas et on continue )
  * 
  *
  * @author loubna TALEB 2024 
  *         
  */
 public class CepsGHAthinnerCompostion extends AbstractGroupableIntervener implements Intervener, GroupableIntervener {
    //public class CepsGHAThinner2 implements Intervener, GroupableIntervener {
	 
	 // fc-8.6.2020 Added AbstractGroupableIntervener for getSceneArea (scene)
 
	 static {
        Translator.addBundle("forceps.extension.intervener.CepsGHAThinner2");
    }

    // nb-13.08.2018
    //public static final String NAME = "CepsGHAThinner2";
    //public static final String VERSION = "1.0";
    //public static final String AUTHOR = "X. Morin, B. Cornet, F. de Coligny";
    //public static final String DESCRIPTION = "CepsGHAThinner2.description";

    // nb-30.08.2018
    //static final public String SUBTYPE = "SelectiveThinner"; // fc-4.12.2014
                                                                // added final
                                                                // (reviewing
                                                                // static
                                                                // variables
                                                                // after a
                                                                // Simmem bug)
                                                                private boolean constructionCompleted = false; // if cancel in interactive
                                                                // mode, false
            
                // Parameters
            
                protected double param_minCutG; // m2/ha
                protected double param_type; // [0, 1] from below, from above
                protected double param_finalG; // m2/ha G to be reached after thinning
                protected double param_finalGpercentage = -1; // optional, if set, in [0,
                                                                // 100] if
                // >= 0, param_finalG is calculated in
                // init ()
    
	 // Expected species mix after intervention, in percentage for each species,
	 // sum percentages <= 100%
	 // e.g. "AAlb-60%, FSyl-30%" (and 10% of other species)
	 protected String param_expectedMixComposition;
 
	 // Parameters
 
	 private Set<String> expectedMix; // e.g. AAlb, FSyl
	 private Map<String, Double> mixMap; // e.g. AAlb->60 Fsyl->30
 
	 // sNames of the trees in the scene
	 private Set<String> presentSNames;
     protected CepsScene scene; // Reference stand: will be altered by apply ()
	 private CepsInitialParameters ip;
 
	 private List<CepsTree> concernedTrees;
	 private double initG; // m2/ha
	 
    private BufferedWriter logger;

    // Méthode pour initialiser le logger
    private void initLogger(String outputDir) throws IOException {
        File file = new File(outputDir, "forceps.inv");
        if (!file.exists()) {
            file.createNewFile();
        }
        logger = new BufferedWriter(new FileWriter(file, true));  // true pour append
        logger.write("Composition Initiale: esp:proportion\n");
    }
    // Méthode pour écrire les détails des arbres et les compositions
    private void logDetails(String header, String composition) throws IOException {
       
        logger.write(header);
        //logger.write("la surface terriere initiale :"+initG+"\n");
        //logger.write("le type d'eclairci :"+param_type +"\n");
        logger.write(composition+ "\n");
        
        logger.write("\n");
    }
    // Méthode pour logger les détails des arbres concernés
    private void logTreesDetails(List<CepsTree> trees) throws IOException {
        Map<String, Map<Integer, Set<CepsTree>>> speciesPatchMap = new HashMap<>();
        logger.write("Details des arbres concernes:\n");
        logger.write(" Espece; patch; tree;diametre;BasalArea;age\n");
        // Regrouper les arbres par espèce et patch
        for (CepsTree tree : trees) {
            String species = tree.getSpecies().sname;
            int patchId = tree.getPatchId();

            speciesPatchMap.putIfAbsent(species, new HashMap<>());
            speciesPatchMap.get(species).putIfAbsent(patchId, new HashSet<>());
            speciesPatchMap.get(species).get(patchId).add(tree);
        }

        // Écrire les informations pour chaque espèce et chaque patch
        for (Map.Entry<String, Map<Integer, Set<CepsTree>>> speciesEntry : speciesPatchMap.entrySet()) {
            for (Map.Entry<Integer, Set<CepsTree>> patchEntry : speciesEntry.getValue().entrySet()) {
                for (CepsTree tree : patchEntry.getValue()) {
                    
                    logger.write(String.format("%s; %d; %d; %.2f; %.2f; %d\n",
                            speciesEntry.getKey(),
                            patchEntry.getKey(),
                            tree.getTreeIdInPatch(),
                            tree.getDbh(),
                            tree.getBasalArea(),
                            tree.getAge()));
                }
            }
        }
        logger.write("\n");
    }
    private void closeLogger() throws IOException {
        if (logger != null) {
            logger.close();
        }
    }
    /**
	  * Default constructor.
	  */
    public CepsGHAthinnerCompostion() {
    }
    /**
	  * Script constructor.
	  * 
	  * @param targetGHA
	  *            is a double and corresponds to the target in m2/ha (i.e.
	  *            final, remaining after intervention) GHA - must be within
	  *            possible limits
	  * @param param_type
	  *            [0,1] : 0 for a from below thinning - 1 for a from above
	  *            thinning
	  * @throws Exception
	  */
	 public CepsGHAthinnerCompostion(double minCutG, double param_type, String finalGtext, String param_expectedMixComposition)
     throws Exception {
            //initLogger();
            setMinCutG(minCutG);
            
            setType(param_type);

            // FinalG is tricky, can be absolute: 15.7 m2 or relative: 32%
            setFinalG(finalGtext);
            
            setExpectedMixComposition(param_expectedMixComposition);
    }
    protected void setMinCutG(double minCutG) throws Exception {
        this.param_minCutG = minCutG;
        if (minCutG < 0)
            throw new Exception("param_minCutG must be positive or null");
    }

    protected void setType(double param_type) throws Exception {
        this.param_type = param_type;
        if (param_type < 0 || param_type > 1)
            throw new Exception("param_type must be in [0, 1]");

    }

    protected void setFinalG(String finalGtext) throws Exception {

        try {
            // if number, absolute value, take as is
            this.param_finalG = Double.parseDouble(finalGtext);
        } catch (Exception e) {
            try {
                // if not a number, we expect a percentage like: 30%
                String token = finalGtext.trim();
                if (!token.contains("%"))
                    throw new Exception();
                token = token.replace("%", "").trim();
                param_finalGpercentage = Double.parseDouble(token);
                if (param_finalGpercentage < 0 || param_finalGpercentage > 100)
                    throw new Exception();

            } catch (Exception e2) {
                throw new Exception(
                        "could not evaluate param_finalG, should be a number (absolute value in m2/ha) or a percentage with a '%'");
            }

        }

    }

    protected void setExpectedMixComposition(String param_expectedMixComposition) throws Exception {

        if (param_expectedMixComposition == null || param_expectedMixComposition.length() == 0)
            throw new Exception("missing expected mix composition");

        this.param_expectedMixComposition = param_expectedMixComposition;
        expectedMix = new HashSet<>();
        mixMap = new HashMap<>();

        double mixPercentageControl = 0;

        StringTokenizer st = new StringTokenizer(param_expectedMixComposition, ", ");
        while (st.hasMoreTokens()) {

            try {
                String token = st.nextToken().trim();

                int separatorIndex = token.indexOf("-");
                String sName = token.substring(0, separatorIndex).trim(); // e.g.
                                                                            // AAlb
                String p = token.substring(separatorIndex + 1);
                double percentage = Double.parseDouble(p);

                if (percentage < 0 || percentage > 100)
                    throw new Exception("wrong mix composition value for: " + sName);

                expectedMix.add(sName);
                mixMap.put(sName, percentage);

                mixPercentageControl += percentage;

            } catch (Exception e) {
                throw new Exception("could not evaluate an expected mix composition", e);
            }

        }

        if (mixPercentageControl > 100)
            throw new Exception("error in param_expectedMixComposition, sum of percentages must be lower than 100");

    }

    @Override
    public void init(GModel m, Step s, GScene gscene, Collection c) {

        // This is referentStand.getInterventionBase ();
        scene = (CepsScene) gscene;
        ip = (CepsInitialParameters) m.getSettings();

        // The trees that can be cut
        if (c == null) {
            concernedTrees = scene.getTrees();
        } else {
            concernedTrees = new ArrayList<CepsTree>(c);
        }

        initG = getGha(concernedTrees);

        presentSNames = new HashSet<>();
        for (CepsTree t : concernedTrees) {
            presentSNames.add(t.getSpecies().sname);
        }

        constructionCompleted = true;

    }

    @Override
    public boolean initGUI() throws Exception {
        // Interactive start
       /* epsGHAThinnerDialog2 dlg = new CepsGHAThinnerDialog2(this);

        constructionCompleted = false;
        if (dlg.isValidDialog()) {
            constructionCompleted = true;
        }
        dlg.dispose();*/

        return true;

    }

    /**
     * Extension dynamic compatibility mechanism. This matchWith method checks
     * if the extension can deal (i.e. is compatible) with the referent.
     */
    static public boolean matchWith(Object referent) {
        try {
            return referent instanceof CepsModel;

        } catch (Exception e) {
            Log.println(Log.ERROR, "CepsGHAThinner2.matchWith ()", "Error in matchWith () (returned false)", e);
            return false;
        }

    }

    @Override
    public String getName() {
        return Translator.swap("CepsGHAThinner2.name");
    }

    @Override
    public String getAuthor() {
        return "X. Morin, B. Cornet, F. de Coligny";
    }

    @Override
    public String getDescription() {
        return Translator.swap("CepsGHAThinner2.description");
    }

    @Override
    public String getVersion() {
        return "1.0";
    }

    @Override
    public String getSubType() {
        return Translator.swap("CepsGHAThinner2.subType");
    }

    /**
     * GroupableIntervener interface. This intervener acts on trees, tree groups
     * can be processed.
     */
    public GroupableType getGrouperType() {
        return TreeList.GROUP_ALIVE_TREE;
    }

    /**
     * Returns the cumulated basal area of the given trees (m2/ha)
     */
    protected double getGha(List<CepsTree> trees) {

        double gha = 0;
        for (CepsTree t : trees) {
            gha += getGHA(t);
        }

        return gha;
    }

    private double getGHA(Tree t) {
        double g = Math.pow(t.getDbh() / 100d, 2d) * Math.PI / 4d;
        
        // fc-8.6.2020 considers group area is any
        double gHa = g * 10000d / getSceneArea (scene);
//		double gHa = g * 10000d / scene.getArea();
        
        return gHa;
    }

    /**
     * Returns the trees with the given sName
     */
    protected List<CepsTree> getTrees(List<CepsTree> candidateTrees, Set<String> expectedMix, String sName) {

        // StringBuffer b = new StringBuffer ("getTrees ("+sName+")... ");

        List<CepsTree> trees = new ArrayList<>();

        for (CepsTree t : candidateTrees) {

            boolean treeIsSName = expectedMix.contains(sName) && t.getSpecies().sname.equals(sName);
            boolean treeIsOtherSp = sName.equals("otherSp") && !expectedMix.contains(t.getSpecies().sname);

            if (treeIsSName || treeIsOtherSp) {
                // b.append(t.getSpecies().sname+", ");
                trees.add(t);
            }
        }

        // System.out.println(b.toString ());

        return trees;
    }

    /**
     * These assertions are checked at the beginning of apply () in script AND
     * interactive mode.
     *
     */
    private boolean assertionsAreOk() {

        if (scene == null) {
            Log.println(Log.ERROR, "CepsGHAThinner2.assertionsAreOk ()",
                    "scene is null. CepsGHAThinner2 is not appliable.");
            return false;
        }

        return true;
    }

    /**
     * Intervener interface. Controls input parameters.
     */
    public boolean isReadyToApply() {
        // Cancel on dialog in interactive mode -> constructionCompleted = false
        if (constructionCompleted && assertionsAreOk()) {
            return true;
        }
        return false;
    }
    private Map<String, List<ScoredTree>> sortTrees(Set<String>expectedMix){
       //Dictionnaire dont la cle est l'espece et sa valeur est une liste des arbres de cette espece
       HashMap<String,List<ScoredTree> > sortedTree=new HashMap<String,List<ScoredTree>>();
       double type;
       double randomness=0 ;
       if (param_type >= 0 && param_type <= 0.5) {
         randomness =(2d*param_type);
        type=0d; // from below
       } else if (param_type <= 1) {
        randomness = 2d - 2d * param_type;
        type=1d; // from above
       }
       //Définir les paramétres de score alpha 
       double ci;
       Random random=new Random();
       double uniformProba;//quand tp=0.5
       double probaOfBeingCut;//
       double score ;//alpha 
       double rangeMax;//le dénominateur
       double circOfMaxProba;//pour regler le deno en fonction entre tp=0.5 et tp=1
       //Calculer Cmax et Cmix pour tous les espèces dans l'inetrvention donc ça
       //change pas après chaque éclairci 
       double cMin=1000d;
       double cMax=0d;
       for (Iterator i=concernedTrees.iterator();i.hasNext();){
           Tree t=(Tree) i.next();
           ci=t.getDbh() *Math.PI;
           if(ci <cMin){
               cMin=ci;//
           }
           if (ci >cMax) {
               cMax=ci;
           }
       }
       //Calculer le deno pour tp=0 et 1
       circOfMaxProba=param_type*(cMax -cMin)+cMin;
       rangeMax=circOfMaxProba-cMin+1;//pour tp=1=>Cmax-Cmin+1
       //cas tp=0 =>circofMaxProba=Cmin donc rangeMax=1
       if ((-circOfMaxProba+cMax+1)>rangeMax) {
           rangeMax=(-circOfMaxProba+cMax+1);
       }
       //trier pour chaque espèce dans expeceted et l'ajouter dans sortTree
       //pour chaque espèce dans expected
       for (String name:expectedMix) {
           List<ScoredTree> arrayTree=new ArrayList<ScoredTree>();
           //identifiant de l'ensemble des arbres pour l'espece name
           List<CepsTree> sNameTrees=getTrees(concernedTrees, expectedMix, name);
           for (Iterator i=sNameTrees.iterator();i.hasNext();){
               Tree t=(Tree) i.next();
               ci=t.getDbh()*Math.PI;
               uniformProba =random.nextDouble();
               probaOfBeingCut=1-Math.abs(ci-circOfMaxProba)/rangeMax;
               score=randomness*uniformProba+(1-randomness)*probaOfBeingCut;
               ScoredTree scoredTree=new ScoredTree(t, score);
               arrayTree.add(scoredTree);
               
   
           }
           //trier les arbres de l'espèce name
           Collections.sort(arrayTree);
          //ajouter arrayTree dans sortedTree
          sortedTree.put(name,arrayTree);
         
       }
       

       /*System.out.println("Afficher les scores pour verifier qu'il sont triee dans l'ordre croissant du score :");
       for (String species : expectedMix) {
           List<ScoredTree> trees = sortedTree.get(species);
           System.out.println("Arbres triés pour l'espèce " + species + ":");
           for (ScoredTree st : trees) {
               System.out.println("Arbre ID: " + st.getTree().getId() + ", Score: " + st.getScore());
           }
       }*/

       return sortedTree;
   
    }
     /*Select k : dans le dictionnaire triée sortedTree, on selectionne les k premiers 
     * pour 5 especes on choisit :k1,k2,k3,k4,k5
     *Parametres :SortedTree : dictionnaire trié des arbres
     *return :List<Cepstree>:listes des premiers arbres triées selon le score et le
     *type d'éclairci tp ={0,0.5,1}
     */
     private List<Tree> selectkTree(Map<String, List<ScoredTree>> sortedTree) {
       List<Tree> kTrees = new ArrayList<>();
       for(String name:sortedTree.keySet()){
           List<ScoredTree> arrayTree=sortedTree.get(name);
           if (!arrayTree.isEmpty()) { // Assurer qu'il y a au moins un arbre dans la liste
           kTrees.add(arrayTree.get(0).getTree()); // Ajouter le premier arbre sans le score
           
       }
       }
       
       /*for (int i = 0; i < kTrees.size(); i++) {
           System.out.println("les K premiers arbres  : " + kTrees.get(i).getId());
       }*/
       return kTrees;
     }
      /*Composition_new: On doit calculer la composition actuel après chaque coupe pendant
      * l'intervention pour la comparer avec la composition cible 
      * Parametres : Tree : l'arbre qu'on choisit à couper 
      *              G_esp:la surface actuelle de l'espece esp m2/ha 
      *              G_init: la surface initiale de l'espece esp m2/ha
      * return : double (G_esp-G_tree)/G-init 
      */
     private Double Composition_new(Tree t,Double G_esp,Double G_init_esp){
       Double G_tree=getGHA(t);
       return (G_esp-G_tree)/G_init_esp;
     }
     /*Composition_act:je recupère le dictionnaire de la composition actuelle après la coupe de l'arbre k 
      * parmi les différents premiers arbres k.
      * Parametres : expectedMix :les differents especes qui existe 
      *              MapG_init : la liste de la surface initiale de chaque espece
      *              Tree t :l'arbre de l'espece esp.
      * 			 G_esp_act:en m2/ha la surface terriere actuelle en m2/ha 
      * Return : retourner la composition de tous les especes après la coupe de l'arbre t  en %
      */
     private Map<String, Double> Composition_act(Set<String> expectedMix, Double G_int, Tree t,Map<String,Double>G_esp_act) {
       Map<String, Double> C_act = new HashMap<>();
       Double C_a = 0.0d;
   
       
       String speciesOfTree = (t instanceof CepsTree) ? ((CepsTree) t).getSpecies().sname : "Unknown";
   
       for (String name : expectedMix) {
           //attrubuer à chaque espece sa surface initiale 
           Double G_esp = G_esp_act.get(name);
           
           
           if (G_int != 0.0d) {
               if (name.equals(speciesOfTree)) {
                   Double G_tree = getGHA(t); // Assurez-vous que cette méthode est correcte pour obtenir la contribution de t
                   C_a = (G_esp - G_tree)*100d / G_int; // Recalcul après coupe
                   //G_esp_act.put(name,G_esp-G_tree);
                   //System.out.println("la composition a changé:"+C_a);
               } else {
                   C_a = G_esp*100d / G_int; // Calcul normal
                   //G_esp_act.put(name,G_esp);
                   //System.out.println("la composition n'a pas changé:"+C_a);
               }
               C_act.put(name, C_a);
           }
           
       }
       return C_act;
   }
    /*norme_k :calculer la différence entre la composition avec la coupe de l'arbre  k 
     *Parametres : Ck_act la composition actuelle avec la coupe de l'arbre k
     *             mixMap: la composition cible mais en proportion {0,0.1,0.2,........0.9,1}
     *Return :  la norme entre ||Ck_act-mixMap||
     */
     public double calculateNorm(Map<String, Double> currentComposition) {
       double sumOfSquares = 0.0;

       // On itère sur l'ensemble des clés (espèces) de la composition cible
       for (Map.Entry<String, Double> entry : mixMap.entrySet()) {
           String species = entry.getKey();
           double targetPercentage = entry.getValue();
           double currentPercentage = currentComposition.getOrDefault(species, 0.0);

           // Calcul de la différence au carré pour chaque espèce
           
           sumOfSquares += Math.abs(currentPercentage-targetPercentage );
           
       }

       
       //System.out.println("la norme de la difference du  :"+Math.sqrt(sumOfSquares));
       // Racine carrée de la somme des carrés pour obtenir la norme euclidienne
       return Math.sqrt(sumOfSquares);
   }
   
    private void updateSpeciesAreaAfterCut(Tree tree, Map<String, Double> speciesArea) {
        String species = ((CepsTree) tree).getSpecies().sname;
        double areaRemoved = getGHA(tree);
        speciesArea.computeIfPresent(species, (k, v) -> v - areaRemoved);
    }
    private void  updateGk_act(Tree tree,Map<String,Double> Gk_esp){
       String speciesOfTree = (tree instanceof CepsTree) ? ((CepsTree) tree).getSpecies().sname : "Unknown";
   
       for (String name : expectedMix) {
           //attrubuer à chaque espece sa surface initiale 
         Double G_esp=Gk_esp.get(speciesOfTree);
         if (name.equals(speciesOfTree)) {
                   Double G_tree = getGHA(tree);
                   G_esp -= G_tree; 
                   
               } 
               Gk_esp.put(name, G_esp);
          
           
       }
       
    }
        
     public Object apply() throws Exception {
      // Initialize logging at the beginning of the apply method
      initLogger("/home/loubna/ca/data/forceps/BasicVersion");
        System.out.println("le type d'eclairci est :"+param_type);
       // Initial checks and calculations
       if (param_finalGpercentage >= 0)
           this.param_finalG = initG * param_finalGpercentage / 100d;
       if (param_finalG < 0)
           throw new Exception("error, param_finalG: " + param_finalG + " must be positive");
   
       double sum = 0;
       for (String sName : mixMap.keySet()) {
           double v = mixMap.get(sName);
           sum += v;
       }
       if (sum > 100)
           throw new Exception("error in expected mix map, sum of percentages must be lower than 100: " + sum);
       if (!isReadyToApply())
           throw new Exception("CepsGHAThinner2.apply () - Wrong input parameters, see Log");
   
       scene.setInterventionResult(true);
       if (param_finalG > initG) {
           Alert.print("CepsGHAThinner2.apply (): param_finalG: " + param_finalG + " is lower than initG: " + initG + ", cut nothing");
           return scene;
       }
   
       Double G_cut = 0.0d;
       Map<String, List<ScoredTree>> sortedTree = sortTrees(expectedMix);
      /* *System.out.println("les differents especes dans sortedTree");
       for (Map.Entry<String, List<ScoredTree>> entry : sortedTree.entrySet()) {
           String key = entry.getKey();
           List<ScoredTree> value = entry.getValue();
           if (key.equals("PSyl")) {
               System.out.println("Key: " + key + ", Value: " + value);
           }
       }*/
       //Map<String, Double> G_esp_act = new HashMap<>();
       Double G_int = initG;
       Double pourcentage=0.0d;
       //calculer la surface initiale de surfaces terrieres  pour chaque espece
       Map<String, Double> G_esp=new HashMap<>();
       for (String name:expectedMix){
        List<CepsTree>NamesTree=getTrees(concernedTrees, expectedMix, name);
        G_esp.put(name,getGha(NamesTree));
       }
       
       int i=0;
       
       while (param_finalG < initG - G_cut) {
           i+=1;
           G_int-=G_cut;
           //select les k_tree_arbre premiers;
           List<Tree> K_trees=selectkTree(sortedTree);
           //selctionner l'arbre dans la norme est minimale :
           if (K_trees.isEmpty()){
            System.out.println("la liste K_tree est vide : on sort "); 
            break;
           }
           
           Tree minTree=null;
           Double min=Double.MAX_VALUE;
           Double norm=0d;
           System.out.println("les Ktree arbre selectionne");
           for (Tree tree:K_trees){
                Map<String,Double> Compk_act=Composition_act(expectedMix, G_int, tree, G_esp);
                norm=calculateNorm(Compk_act);
                String speciesOfTree = (tree instanceof CepsTree) ? ((CepsTree) tree).getSpecies().sname : "Unknown";
                System.out.println("l'arbre: "+tree.getId()+"de l'espece :"+speciesOfTree +" avec un diametre"+tree.getDbh());
                System.out.println("dont  la norme de difference est :"+norm);
               
                if(norm<min){
                    min=norm;
                    minTree=tree;
                }
           }
           
           //Couper minTree de la scene:
           if (minTree!=null){
            String speciesOfTree = (minTree instanceof CepsTree) ? ((CepsTree) minTree).getSpecies().sname : "Unknown";
            scene.removeTree(minTree);
            removeTreeFromSortedTree(minTree, sortedTree);
            updateGk_act(minTree,G_esp);
            G_cut+=getGHA(minTree);
            System.out.println("la surface terriere restante:"+G_int);
            System.out.println("l'arbre :"+minTree.getId()+"de l'espece "+speciesOfTree+ " est coupee  avec une norme min="+min);
            if(param_finalG>G_int) {
                System.out.println("G_int:"+initG+ " G_obj est :"+param_finalG+" et G_rest:"+G_int);
                break;
               
               }


           }
          
       }
       System.out.println("CepsGHAThinner2: avant coupe : " + traceSceneComposition(concernedTrees));
       System.out.println("CepsGHAThinner2:La composition cible est : "+param_expectedMixComposition);
       System.out.println("CepsGHAThinner2: apres coupe: " + traceSceneComposition(scene.getTrees()));
       System.out.println("CepsGHAThinner2: param_finalG: " + param_finalG + " et  la surface restante apres coupe   " + G_int);
       logDetails("Intervention Composition Initiale:\n", traceSceneComposition(concernedTrees));
        logDetails("Composition Cible:\n", param_expectedMixComposition);
        logDetails("Composition Finale:\n",traceSceneComposition(scene.getTrees()) );
         // Log les détails des arbres concernés
         logTreesDetails(concernedTrees);

         // Fermeture du fichier
         closeLogger();
       
       return scene;
   }

 

// Helper method to remove a tree from the sorted trees structure
private void removeTreeFromSortedTree(Tree tree, Map<String, List<ScoredTree>> sortedTree) {
   for (List<ScoredTree> list : sortedTree.values()) {
       list.removeIf(scoredTree -> scoredTree.getTree().equals(tree));
       //System.out.println("l'arbre :"+tree.getId()+"est coupee ");
   }
}
    private String traceSceneComposition(List<CepsTree> trees) {
        StringBuffer b = new StringBuffer("");

        // fc-1.12.2021 AdditionMap key type now generic, added <String>
        AdditionMap<String> map = new AdditionMap<>();
        double totalGHA = 0d;
        for (CepsTree t : trees) {
            String sName = t.getSpecies().sname;
            double gha = getGHA(t);
            map.addValue(sName, gha);
            totalGHA += gha;
        }

        for (String sName : map.getKeys()) {
            double gha = map.getValue(sName);
            double percentage = gha / totalGHA * 100d;

            b.append(" " + sName + ": " +  " " + percentage + "%");
        }

        return b.toString();
    }

    private String traceMap(Map<String, Double> map) {
        String s = AmapTools.toString(map).replace('\n', ' ');
        s = s.replace("  ", " ");
        return s;
    }

    
    



    /**
     * toString () method.
     */
    public String toString() {
        // nb-13.08.2018
        //return "class=" + getClass().getName() + " name=" + NAME + " constructionCompleted=" + constructionCompleted
        return "class=" + getClass().getName() + " name=" + getName() + " constructionCompleted=" + constructionCompleted
                + " stand=" + scene + " param_minCutG =" + param_minCutG + " param_type =" + param_type
                + " param_finalG =" + param_finalG + " param_expectedMixComposition: " + param_expectedMixComposition;
    }

    // fc-14.12.2020 Unused, deprecated
//	public void activate() {
//	}

    /**
     * This class handles the trees with a score of being cut
     */
    protected class ScoredTree implements java.lang.Comparable {

        public Tree t;
        private double score;

        ScoredTree(Tree t, double score) {
            this.t = t;
            this.score = score;
        }

        public double getScore() {
            return score;
        }

        public void setScore(double score) {
            this.score = score;
        }
        public Tree getTree() {
            return t;
        }
        @Override
       public int compareTo(Object scoredTree) {
           double score1 = this.getScore();
           double score2 = ((ScoredTree) scoredTree).getScore();
           return Double.compare(score1, score2);
   }

    }

}
