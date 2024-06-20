
package forceps.myscripts.michelle;

import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

import org.omg.Messaging.SYNC_WITH_TRANSPORT;

import java.util.List;
import java.util.ArrayList;
import java.util.Collections;
import java.lang.Math;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;


import forceps.myscripts.michelle.ManagementIndv;

/**
 * Class grouping a set of individuals in population for genetic algorithm.
 *
 * @author M. Malara - July 2023 & M. Jourdan - March 2024 & change by loubna Avril
 */

public class ManagementPop{
  /** class grouping a set of individuals in population for genetic algorithm
   use ManagementIndv for individuals
  */

  private List<ManagementIndv> individuals; // list of individuals in the population
  private List<Integer> list_id;            // list of individual identifiers
  private int size;                         // population size, number of individuals in the population
  private SimulationFitness simu_fitness;
  private ManagementIndv best_indv;         // best individual in population
  private double best_fitness;               // interest score of best individual


    /* Costructor */
    public ManagementPop(int nb_indv, int inter_max, SimulationFitness simu_fitness) throws Exception {
      /** create a population of nb_indv random individual of size 8*inter_max
      int nb_indv : number of individuals in the population, population size
      int inter_max : maximum number of interventions
      SimulationFitness simu_fitness
      */
      List<ManagementIndv> individuals = new ArrayList<ManagementIndv>();
      List<Integer> list_id = new ArrayList<Integer>();
      ManagementIndv indv;
      double indv_fitness;
      ManagementIndv best_indv =  new ManagementIndv();
      double best_fitness = 0.0d;
      for (int i = 0; i < nb_indv; ++i){
        // create random individuals
        indv = new ManagementIndv(inter_max, simu_fitness);
        individuals.add(indv);
        list_id.add(indv.getId());
        // cheak fitness
        indv_fitness = indv.getFitness();
        if(indv_fitness > best_fitness){
          best_fitness = indv_fitness;
          best_indv = indv;
        }
      }
      this.simu_fitness = simu_fitness;
      this.individuals = individuals;
      this.list_id = list_id;
      this.size = nb_indv;
      this.best_fitness = best_fitness;
      if(nb_indv > 0){ // else there no best_indv
        this.best_indv = best_indv;
      }
    }


    public ManagementPop(ManagementIndv indv){
      /** create a population composed of a single individual
      ManagementIndv indv : the only individual in the population
      */
      List<ManagementIndv> individuals = new ArrayList<ManagementIndv>();
      List<Integer> list_id = new ArrayList<Integer>();
      double indv_fitness;
      ManagementIndv best_indv =  new ManagementIndv();
      double best_fitness = 0.0d;
      individuals.add(indv);
      list_id.add(indv.getId());
      this.simu_fitness = indv.getSimuFitness();
      this.individuals = individuals;
      this.list_id = list_id;
      this.size = 1;
      this.best_fitness = indv.getFitness();
      this.best_indv = indv;
    }


    public ManagementPop(List<ManagementIndv> individuals){
      /** create a population composed of a set of individuals
      List<ManagementIndv> individuals : set of individuals
      */
      List<Integer> list_id = new ArrayList<Integer>();
      double indv_fitness;
      ManagementIndv best_indv =  new ManagementIndv();
      double best_fitness = 0.0d;
      for (ManagementIndv indv : individuals){
        // create random individuals
        list_id.add(indv.getId());
        // cheak fitness
        indv_fitness = indv.getFitness();
        if(indv_fitness > best_fitness){
          best_fitness = indv_fitness;
          best_indv = indv;
        }
      }
      this.simu_fitness = simu_fitness;
      this.individuals = individuals;
      this.list_id = list_id;
      this.size = individuals.size();
      this.best_fitness = best_fitness;
      this.best_indv = best_indv;
    }


  /* Printer */
  @Override
  public String toString(){
    return("Population of " + this.size + " individuals. Best fitness = " +
     this.best_fitness + ".");
  }


  /* Getter */
  public int getSize(){
    return this.size;
  }


  public List<ManagementIndv> getIndividuals(){
    return this.individuals;
  }


  public ManagementIndv getIndividu(int i){
    return this.individuals.get(i);
  }


  public double getBestFitness(){
    return this.best_fitness;
  }


  public ManagementIndv getBestIndv(){
    return this.best_indv;
  }


  /* Public Functions */
  public void selection(int best_to_parent){
    /** select best_to_parent individuals to be parents
    modify individuals and size
    */
    double fitness_to_parent = this.calcRankFitness(best_to_parent);
    int size_survivor = 0;
    List<ManagementIndv> survivor = new ArrayList<ManagementIndv>();
    List<Integer> id_survivor = new ArrayList<Integer>();
    double indv_fitness;
    double p_survivor;
    Random rn = new Random();
    double rv;
    for(ManagementIndv indv : this.individuals) {
      indv_fitness  = indv.getFitness();
      p_survivor = indv_fitness / this.best_fitness; // calc survival proba
      rv = rn.nextDouble();                           // random variable
      if(rv <= p_survivor || indv_fitness >= fitness_to_parent){
        // the individual survive || is one of the best so is automaticaly save
        survivor.add(indv);
        id_survivor.add(indv.getId());
        ++size_survivor;
      }
    }
    System.out.println("On a sauver cette individu:"+survivor);
    // update individuals and size
    this.individuals = survivor;
    this.size = size_survivor;
    this.list_id = id_survivor;
  }

//change by loubna 
  public void crossover(ManagementIndv parent1, ManagementIndv parent2,
                        double proba_mutation) throws Exception {
    /** un crossover un par un pour les genes non nulles et par paquts du mutilple de 8 
     * pour les zeros 
    */
    System.out.println("on commence le  crossover :avec parent :"+parent1+"et"+parent2);
    List<Double> genome1 = new ArrayList<Double>();//un enfant par couple de parents
    List<Double> genome2 = new ArrayList<Double>();//le deuxiéme enfant par couple de parents
    
    double test0;
    int theta;
    

    // calculate mixed genomes : on ajoute les 5 genes au 3 =>8 donc si intermax=16 donc _*16=128
    int cdt = parent1.getInterMax()*8;
    System.out.println("Voici la taille du genome :"+cdt );
    for (int i=0;i<cdt;i+=8) {
      System.out .println("voici la "+i+" crossover ");
      boolean parent_1_is_null=isNullserie(parent1.getGenome(),i,8);
      boolean parent_2_is_null=isNullserie(parent2.getGenome(), i, 8);
      // crossover null:les deux parents sont nulles 
      if (parent_1_is_null && parent_2_is_null) 
      { 
        
        for (int j=0;j<8;j++){
          genome1.add(parent1.getGene(i+j));
          genome2.add(parent2.getGene(i+j));
        }
        System.out.println("les deux parents ont des genes nulles de"+ i+ "sequences  donc enfant1:"+genome1);
        System.out.println("les deux parents ont des genes nulles de"+ i+" sequences  donc enfant2 :"+genome2);
      }
      else if (parent_1_is_null){
        //parents 1 est nulles
        //l'enfant 1 prend parent 1 et et enfant 2 prend parent 2
        System.out.println("le parent  1 est nulle  :"+parent1);;
        for (int j=0;j<8;j++){
          genome1.add(parent1.getGene(i+j));
          genome2.add(parent2.getGene(i+j));
          
        }
        System.out.println("enfant 1:"+genome1);
        System.out.println("enfant 2:"+genome2);
      }
      else if (parent_2_is_null){
        //parent 2 est nulles 
        System.out.println("le parent  2 est nulle  :"+parent1);;
        for (int j=0;j<8;j++){
          genome1.add(parent1.getGene(i+j));
          genome2.add(parent2.getGene(i+j));
         
        }
        System.out.println("le deuxieme parents a 8 nulles donc enfants 1:"+genome2);
        System.out.println("le premier enfants donc :"+genome1);
      }else {
        //cross over normal un par un et par paquet de 5 pour la composition 
        System.out.println("on commence le crossover (les deux parents ne sont pas nulles)point à point pour l'indice :"+i+"et le gene 1:"+parent1.getGene(i)+"et le gene 2:"+parent2.getGene(i));
        System.out.println("le parent 1 est :"+parent1+ "et de genome :"+parent1.getGenome());
        System.out.println("le parent 2 est :"+parent2+ "et de genome :"+parent2.getGenome());
        boolean pair = false;
        for (int j=0;j<3;j++){
          if (j%2==0) {
            genome1.add(parent1.getGene(i+j));
            genome2.add(parent2.getGene(i+j));
          }else{
            genome1.add(parent2.getGene(i+j));
            genome2.add(parent1.getGene(i+j));
          }
        }
        System.out.print("le crossover pour les 3 premiers genes  donne:");
        System.out.println(" ses enfants 1 :"+genome1+" et enfants 2:"+genome2);
        if(pair){
          for (int j=3;j<8;j++){
            genome1.add(parent1.getGene(i+j));
            genome2.add(parent2.getGene(i+j));
          }
        }else{
          for (int j=3;j<8;j++){
          genome1.add(parent2.getGene(i+j));
          genome2.add(parent1.getGene(i+j));
        }
        System.out.print("le crossover pour les 3 derniers genes donnent :");
        System.out.println(" ses enfants 1 :"+genome1+" et enfants 2:"+genome2);
      }
        pair=!pair;
      }
      

      }
    
    // mutation sur un des genes des 2 enfants 
    genome1 = this.mutation(genome1, parent1.getAllTP(), parent1.getAllGobj(), proba_mutation,parent1.getAllCf_k());
    genome2 = this.mutation(genome2, parent1.getAllTP(), parent1.getAllGobj(), proba_mutation,parent1.getAllCf_k());
    // add in pop
    if(!parent1.sameGenome(genome1)){ // add child 1 in pop if it is different
      System.out.println("le genome 1 est different du parent 1");
      ManagementIndv child1 = new ManagementIndv(genome1, this.simu_fitness, false);

      this.individuals.add(child1);
      this.list_id.add(child1.getId());
      this.size += 1;
    }
    else{ // add parent in pop if not
      this.individuals.add(parent1);
      this.list_id.add(parent1.getId());
      this.size += 1;
    }
    if(!parent2.sameGenome(genome2)){ // add child 2 in pop if it is different
      System.out.println("le genome 2 est different du parent 2");
      ManagementIndv child2 = new ManagementIndv(genome2, this.simu_fitness, false);
      this.individuals.add(child2);
      this.list_id.add(child2.getId());
      this.size += 1;
    }
    else{ // add parent in pop if not
      this.individuals.add(parent2);
      this.list_id.add(parent2.getId());
      this.size += 1;
    }
  }
  //verifier que le genome est nulle sur une sequence 
private boolean isNullserie(List<Double> parent,int start,int length){
  for (int i=start;i<start+length;i++) {
    if (parent.get(i)!=0) return false;

  }
  return true ;
}

  private boolean test0(ManagementIndv parent1, ManagementIndv parent2, int i){
    /** test if one of gene i is 0 for crossover 
    return boolean
    */
    return Double.min(parent1.getGene(i), parent2.getGene(i)) < 0.01d;
  }

  private boolean testCrossoverCondition(ManagementIndv parent1, ManagementIndv parent2, int i) {
    // Test if any of the first three genes is zero
    /*et ajouter aussi le cas ou les quintplets 
     * de la composition sont nuls en gros ce cas est déjà hors d'espace de contraintes 
     * car il faut laisser au moins 2 especes traiter parmi les 5 species  */
    // Test if all five genes in the quintuplet are zero
    boolean allZero = true;
    for (int j = 3; j < 8; j++) {  // Les cinq gènes du quintuplet commencent à i+3 et finissent à i+7
        if (Double.min(parent1.getGene(i + j), parent2.getGene(i + j)) >= 0.01) {
            allZero = false;
            break;
        }
    }
    return allZero; // Si tous les cinq gènes du quintuplet sont zéros, autoriser l'alternance
}

  

//on va ajouter la mutation aussi pour les génes avec de la composition 
//mutation selon le principe de explore best :tp :  0.5 en 0/1 et 0/1 en 0.5
//G_obj en dessous ou bien au dessus de G_objt 
//C_fk : permutation entre deux genes proche : maintenant je le fait aléatoire après 
//il faut le faire avec les genes proches pour ne pas trop modifier les génes qui sont loin 
  private List<Double> mutation(List<Double> genome, List<Double> all_tp,
List<Double> all_Gobj, double proba_mutation,List<List<Double>> Cf_k){
      /** applie a mutation to genes of genome with a probability of proba_mutation
      return a mutate genome
      */
      System.out.println("On commence la mutation:");
      Random rn = new Random();
      double rv;
      double gene;
      double g;
      int j;
      int j1;
      int j2;
      int i = 0;
      int nb_tp = all_tp.size();
      int nb_g_obj = all_Gobj.size(); 
      int totalSize = 0;
      for (List<Double> list : Cf_k) {
              totalSize += 1;
      }
      System.out.println("The total size of the Cf_k list is: " + totalSize);
      while(i < genome.size()){
        //voir si la premiere sequence est nulle si oui pas de mutation

        boolean genome_seq_null=isNullserie(genome, i, 8);
        if (genome_seq_null){
          i+=8;
          System.out.println("Pas de mutation car la :"+i+"sequence nulle du genome :"+genome);
          
        }else {
          System.out.println("Commencer la mutation sur l'un des genes de genome");
          i++;//--------------mutation tp 
          rv=rn.nextDouble();
          gene = genome.get(i);
          
          if(rv<proba_mutation){
            //mutattion of type of thinning 
            System.out.println("On fait la mutation sur tp  d'indice :"+i+"et de gene "+genome.get(i)+"dans le genome +"+genome);
            System.out.println("le gene de tp est :"+gene);
            j=rn.nextInt(nb_tp);
            g=genome.set(i, all_tp.get(j));
            }
            i++;//----------mutation G_obj
            rv=rn.nextDouble();
            gene = genome.get(i);
            if(rv<proba_mutation){
              System.out.println("On fait la mutation sur G_obj  d'indice :"+i+"et de gene "+genome.get(i)+"dans le genome +"+genome);
              System.out.println("le gene G_obj  est :"+gene);
                j=rn.nextInt(nb_g_obj);
                g=genome.set(i,all_Gobj.get(j));
          }
          i++;//---------------mutation composition 
          rv=rn.nextDouble();
          if(rv<proba_mutation){
            
              j=rn.nextInt(totalSize);
              List<Double> list =Cf_k.get(j);
              int k=i;
              System.out.println("On fait la mutation sur Cf  à partir  :"+k+"et de gene "+genome.get(k)+"dans le genome +"+genome);
              //System.out.println("le gene  Cf_k est :"+gene);
              for ( Double x :list ){
                System.out.println("Voici le génome :"+genome.get(k) +"d'indice k "+k);
                g=genome.set(k,x);
                k++;
                int f=k-1;
                System.out.println("Voici le génome :"+x +"d'indice k "+f +" donc le génome est :"+genome.get(f));
              }
          }
          i+=5;//---------------mutation composition
        }
        System.out.println("On a finit  la :"+i+"periode ");
      }
      return genome;
    }

public void setCf_genome(List<Double> genome,int i,Random rn ){
  int j1=rn.nextInt(5);
  int j2=rn.nextInt(5);
  double x1=genome.get(i+j1);
  double x2=genome.get(i+j2);
  System.out.println("Avant mutation le genome est :"+genome );
  if (j1!=j2){
    x1=genome.set(j1,x1+10);
    x2=genome.set(j2, x2-10);
    System.out.println("la mutation se fait sur:"+x1 +"et :"+x2+" et donc genome est "+genome);
   }
}


  public void updatePop(int generation_cnt, String output_dir){
    /** removes non-viable individuals from the population,
        update best individu and its fitness,
        writes fitness to the out file
    modify individuals, list_id, size, best_indv and best_fitness
    */
    System.out.println("Voici la fct de la generation adapte");
    try{
      FileWriter fw = new FileWriter(output_dir + "/evolFitness.txt", true);
      int size_viable = 0;
      List<Integer> list_id = new ArrayList<Integer>();
      List<ManagementIndv> viable = new ArrayList<ManagementIndv>();
      double indv_fitness;
      double current_best_fitness = 0.0d;
      ManagementIndv current_best_indv = this.individuals.get(0);
      for(ManagementIndv indv : this.individuals) {
        indv_fitness = indv.getFitness();
        if(indv_fitness > 0.0d){
          // viable
          viable.add(indv);
          list_id.add(indv.getId());
          ++size_viable;
          // writes fitness to the out file
          fw.write(generation_cnt + "	" + indv.getId() + "	" + indv_fitness + "\n");
          if(indv_fitness > current_best_fitness){
            // best
            current_best_fitness = indv_fitness;
            current_best_indv = indv;
          }
        }
      }
      // update
      this.individuals = viable;
      this.list_id = list_id;
      this.size = size_viable;
      this.best_fitness = current_best_fitness;
      this.best_indv = current_best_indv;
      fw.close();
    }
    catch (IOException e) {
      e.printStackTrace();
    }
  }


  public void addToPop(ManagementPop pop){
    /** add to the population any individuals from pop that are not yet present
    modify individuals, list_id, size, best_indv and best_fitness
    */
    System.out.println("Ajouter a la population any ind n'esxiste pas ds pop");
    int size_viable = 0;
    List<ManagementIndv> viable;
    int indv_id;
    double indv_fitness;
    for(ManagementIndv indv : pop.getIndividuals()) {
      indv_id = indv.getId();
      if(!this.list_id.contains(indv_id)){
        // add in pop if is it not
        this.individuals.add(indv);
        this.list_id.add(indv_id);
        ++this.size;
        indv_fitness = indv.getFitness();
        if(indv_fitness > this.best_fitness){
          // replace best
          this.best_fitness = indv_fitness;
          this.best_indv = indv;
        }
      }
    }
  }


  public void addToPop(ManagementIndv indv){
    /** add to the population the individual if it is not yet present
    modify individuals, list_id, size, best_indv and best_fitness
    */
    System.out.println("Ajouter indv a la pop");
    int size_viable = 0;
    List<ManagementIndv> viable;
    int indv_id = indv.getId();
      if(!this.list_id.contains(indv_id)){
        // add in pop if is it not
        this.individuals.add(indv);
        this.list_id.add(indv_id);
        ++this.size;
        double indv_fitness = indv.getFitness();
        if(indv_fitness > this.best_fitness){
          // replace best
          this.best_fitness = indv_fitness;
          this.best_indv = indv;
        }
      }
  }


  public void shuffle(){
    /** shuffle individuals list
    */
    System.out.println("melanger les individus ");
    Collections.shuffle(this.individuals);
  }


  /* Private Functions */
  private double calcRankFitness(int rank){ // ça peut être fait en plus rapide je penses
    /** find the "rank" best individual
    return the fitness of the "rank"th individual
    */
    List<Double> fitness_best =  new ArrayList<Double>();
    double indv_fitness;
    int i = 0;
    while (i < Integer.min(rank, this.size)){
      // recover of the first "rank" individuals and their fitness
      fitness_best.add(this.individuals.get(i).getFitness());
      ++i;
    }
    Collections.sort(fitness_best);
    while(i < this.size){
      // rest of individuals
      indv_fitness = this.individuals.get(i).getFitness();
      if(indv_fitness > fitness_best.get(0)){
        fitness_best.remove(0);
        fitness_best.add(indv_fitness);
        Collections.sort(fitness_best);
      }
      ++i;
    }
    return fitness_best.get(0);
  }


  private void updateFitness(){
    /** found the best fitness af all individuals
    modify best_indv and best_fitness
    */
    double current_best_fitness = 0;
    ManagementIndv current_best_indv = this.individuals.get(0);
    double indv_fitness ;
    for(ManagementIndv indv : individuals){
      indv_fitness = indv.getFitness();
      if(indv_fitness > current_best_fitness){
        current_best_fitness = indv_fitness;
        current_best_indv = indv;
      }
    }
    this.best_fitness = current_best_fitness;
    this.best_indv = current_best_indv;
  }

}

