import java.text.DecimalFormat;
import java.util.*;
import java.security.SecureRandom;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

// resource mode where resources move around and are not injected/dejected, they just move with fixed amounts
static final boolean LONG_WALK_MODE = false;
static final float LONG_WALK_QTY = 0.5;

// total capacity per square. if a square has more than this much stuff in it, it distributes stuff to surrounding squares.
static final float CPS = 40;

static final int SCREEN_WIDTH = 800;

static final int GRID_UNIT = 3;

static final int GRID_WIDTH = 800;
static final int GRID_HEIGHT = 270;

static final int NUM_CHEMS = 5; // food, waste, gas, air, energy

static final float TARGET_POP_MIN = 5000;
static final float TARGET_POP_MAX = 9000;

// indices of elements
static final int FOOD = 0;
static final int WASTE = 1;
static final int GAS = 2;
static final int AIR = 3;
static final int ENERGY = 4; // always the last index

static final String[] SUBSTANCE_LABELS = new String[] { "Food", "Waste", "Gas", "Air", "Energy" };
int nextMaxUpdate = 0;

final List<Substance> substanceList = new ArrayList<Substance>();

static final int GRID_FOOTER = 750;

static final DecimalFormat df = new DecimalFormat("+0.00000;-0.00000");
static final DecimalFormat df0 = new DecimalFormat("0");
static final DecimalFormat df1 = new DecimalFormat("0.0");
static final DecimalFormat df2 = new DecimalFormat("0.00");
static final DecimalFormat df5 = new DecimalFormat("0.00000");

static Map<Integer, Integer> genesToCounts = new HashMap<Integer, Integer>();

float[][][] grid;
int[][][] effectGrid; // 0 = blood, 1 = share food, 2 = share energy
Being[][] beingGrid; // where things live
Listener listener = null;
long beingId = 0;
Map<Long, Being> beingMap = new HashMap<Long, Being>((int) TARGET_POP_MAX);

PFont f1;
PFont f2;
PFont f3;

private static SecureRandom r = new SecureRandom();

public Species globalPopulation = new Species(null, 0, 0, "Global");

public float substanceMin = Float.MAX_VALUE;
public float substanceMax = Float.MIN_VALUE;

static final int NUM_MODS = 4;

/** Number of beings per species to start with **/
static final int INITIAL_POPULATIONS = 2;

/** Number of seed species to create */
static final int SEED_SPECIES = 2000;

int viewMode = 0;
boolean showEffects = true;
boolean paused = false;
int showBeings = 0;

int skipFrames = 0;

float injectionRate = 0.005;

private int speciesId = 0;

private int populateFood = -1;

void keyPressed() {
  if (key == ' ') {
    skipFrames += 100;
  } else if (key == 'f') {
    populateFood = FOOD;
  } else if (key == 'w') {
    populateFood = WASTE;
  } else if (key == 'g') {
    populateFood = GAS;
  } else if (key == 'a') {
    populateFood = AIR;
  } else if (key == 'e') { // show effects of battle and sharing
    showEffects = !showEffects;
    println((!showEffects ? "not " : "") + "showing effects");
  } else if (key == 'p') { // pause
    paused = !paused;
  }
}

class Being {
  public boolean alive = true;

  public Long id = beingId++;

  public boolean moved = false; // reset every turn, used to track beings that have already moved so they don't run twice

  public Species species;

  // for brain:
  public final List<InputModule> inputModules = new ArrayList<InputModule>();

  // for brain:
  public final List<OutputModule> outputModules = new ArrayList<OutputModule>();

  // w&b into hidden layer
  public float[] inputWeights;
  public float[] inputBiases;

  // w&b from hidden layer
  public float[] outputWeights;
  public float[] outputBiases;

  // w&b from hidden layer2
  public float[] outputWeights2;
  public float[] outputBiases2;

  // these things, done in order:
  public final List<Module> modules = new ArrayList<Module>();

  public int offspringAttempts = 0;

  /**
   Module action lifecycle:
   
   suffocate()
   digest()
   respire()
   absorb() & move()
   reproduce()
   replicate()
   attack()
   utility()
   **/

  public float respirationRequirement = 0; // energy
  public float starvationPenalty = 0; // HP damage if energy requirement is not met
  public float respirationModifier = 1;
  public float[] storageCapacities = new float[NUM_CHEMS + 1]; // storage of elements, plus energy
  public float[] storage = new float[NUM_CHEMS + 1]; // storage of elements, plus energy

  public int replicationCount = 0; // number of replicated modules for reproduction

  public float hp = 0; // health
  public float maxHp = 0; // max health

  public float shields = 0; // shields

  public int age = 0;

  // minor mutation rate
  // TODO: make this modularized!
  public float minorMutation = 0.2;

  // major mutation rate
  // TODO: make this modularized!
  public float majorMutation = 0.05;

  // location
  public int x;
  public int y;

  public int primaryFood;

  public Listener listener = null;

  final int requiredReplication; // previously genome size

  final float[] hiddenLayer;
  final float[] hiddenLayer2;
  final float[] outputLayer;

  public Being(Being parent, Species spec, int primaryFood, int myX, int myY) {
    this.x = myX;
    this.y = myY;
    this.primaryFood = primaryFood;
    List<Module> newModules = new ArrayList<Module>(spec.getBirthModules());
    boolean speciated = false;
    int toRemove = -1;
    if (random(1) < majorMutation) { // this seemed to hamper biodiversity: && spec.population < (speciesList.get(0).population * 0.8)) { // add a module unless our population is more than 80% of #1
      speciated = true;
      //TODO: make this modular

      int modChoice = randInt(0, 19);
      int newFood = primaryFood;

      if (modChoice == 0) {
        // for allowing food group mutation:
        //newFood = (primaryFood + 1) % (NUM_CHEMS-1);
        // for not:
        newFood = primaryFood;

        //for (int i = 0; i < 3; i++) {
        //  if (speciesList.size() > 3 && speciesList.get(i).primaryFood == newFood) { // don't speciate diet changes if a top-N species already exists for that food.
        //    newFood = primaryFood;
        //    break;
        //  }
        //}
        for (int i = newModules.size() - 1; i >= 0; i--) {
          if (newModules.get(i) instanceof FoodDigestModule || (newModules.get(i) instanceof StorageModule && !newModules.get(i).getName().contains("Energy"))) { // kill old digestion modules and storage modules
            newModules.remove(i);
          }
        }
        newModules.add(new FoodDigestModule(newFood, random(0.5, 3), random(0.99, 1.01), 0));
        newModules.add(new StorageModule(newFood, random(1, 8)));
      } else if (modChoice == 1) {
        newModules.add(new PrimaryFoodSensor());
      } else if (modChoice == 2) {
        newModules.add(new HealthSensor());
      } else if (modChoice == 3) {
        newModules.add(new PopulationSensor());
      } else if (modChoice == 4) {
        // previously, seemed to work but was a bit stifling to speciation in tight situations :newModules.add(new AttackModule(random(0.1, 1), randInt(1, 2)));
        newModules.add(new AttackModule(normal(0.6, 0.1), normal(0.6, 0.1)));
      } else if (modChoice == 5) {
        newModules.add(new StorageModule(ENERGY, random(1, 4)));
      } else if (modChoice == 6) {
        newModules.add(new StorageModule(newFood, random(1, 4)));
      } else if (modChoice == 7) {
        newModules.add(newMoveModule());
      } else if (modChoice == 8) {
        newModules.add(new RegenModule());
      } else if (modChoice == 9) {
        newModules.add(new ReplicateModule());
      } else if (modChoice == 10) {
        newModules.add(new RespirationModifierModule(random(0.95, 0.99)));
      } else if (modChoice == 11) {
        newModules.add(new HealthModule(normal(1, 1)));
      } else if (modChoice == 12) {
        newModules.add(new MinorMutationModule(random(0.05, 0.2)));
      } else if (modChoice == 13) {
        newModules.add(new MajorMutationModule(random(0.9, 1.1)));
      } else if (modChoice == 14) {
        newModules.add(new DefendModule(random(0, 10)));
      } else if (modChoice == 15) {
        newModules.add(new ShareModule(random(0, 10), ENERGY, random(1) < 0.5));
      } else if (modChoice == 16) {
        newModules.add(new SharePrimaryFoodModule(random(0, 10), random(1) < 0.5));
      } else if (modChoice == 17) {
        newModules.add(new AdjacentAllySensor());
      } else if (modChoice == 18) {
        newModules.add(new AdjacentEnemySensor());
      } else {
        newModules.add(new SubstanceSensor());
      }

      if (newModules.size() > 26 || random(0, 1) > 0.5) { // remove a module when you hit size 20, or when you flip heads
        int fails = 0;
        while (toRemove == -1 && fails < 20) {
          fails++;
          int modIndex = randInt(0, newModules.size() - 1);
          if (!(newModules.get(modIndex) instanceof InherentModule)) {
            toRemove = modIndex;
            newModules.remove(toRemove);
          }
        }
      }
      /* DEFUNCT MODULES:
       newModules.add(new DisperseModule(random(spec.generation / 50f)));
       } else if (modChoice == 13) {
       //newModules.add(new AsexualReproductionModule(0.1 + random(spec.generation / 20f)));
       } else if (modChoice == 14) {
       //newModules.add(new SuffocateModule(randInt(1, Math.max(1, Math.min(spec.generation / 7, 7))), random(1 - (spec.generation / 50f), 2 - (spec.generation / 50f))));
       } else if (modChoice == 15) {
       //newModules.add(new LifeExpectancyModule(1, random(birthModules.size())));
       */

      Integer speciesCount = genesToCounts.get(newModules.size());
      if (speciesCount == null) {
        speciesCount = 0;
      }
      genesToCounts.put(newModules.size(), ++speciesCount);
      spec = new Species(spec, newFood, System.currentTimeMillis(), (spec.generation + 1) + "-" + speciesCount);

      for (Module mod : newModules) {
        Gene g = new Gene();
        g.modules.add(mod);
        spec.genes.add(g);
      }

      //println(spec.name);
      //println(newModules.get(newModules.size() -1).getName() + ": " + newModules.get(newModules.size() -1).getDescription());
    }
    this.species = spec;
    if (!speciesList.contains(species)) {
      speciesList.add(species);
    }

    for (int i = 0; i < newModules.size(); i++) {
      Module myMod = newModules.get(i);
      if (speciated && random(1) < minorMutation) {
        myMod = myMod.mutate(this);
        newModules.set(i, myMod);
      }
      myMod.birth(this);
      modules.add(myMod);

      if (myMod instanceof InputModule) {
        inputModules.add((InputModule) myMod);
      }

      if (myMod instanceof OutputModule) {
        outputModules.add((OutputModule) myMod);
      }
    }

    for (int i = 0; i < newModules.size(); i++) {
      newModules.get(i).postBirth(this);
    }

    hiddenLayer = new float[outputModules.size()];
    hiddenLayer2 = new float[outputModules.size()];
    outputLayer = new float[outputModules.size()];
    inputWeights = new float[inputModules.size() * outputModules.size()];
    inputBiases = new float[outputModules.size()];
    outputWeights = new float[outputModules.size() * outputModules.size()];
    outputBiases = new float[outputModules.size()];
    outputWeights2 = new float[outputModules.size() * outputModules.size()];
    outputBiases2 = new float[outputModules.size()];

    if (parent != null && parent.inputWeights.length <= inputWeights.length && parent.outputWeights2.length <= outputWeights2.length) { // have parent; use parent values as long as our genome has not shrunk
      arrayCopy(parent.outputWeights2, outputWeights2);
      arrayCopy(parent.outputBiases2, outputBiases2);
      arrayCopy(parent.outputWeights, outputWeights);
      arrayCopy(parent.outputBiases, outputBiases);
      arrayCopy(parent.inputWeights, inputWeights);
      arrayCopy(parent.inputBiases, inputBiases);
    }

    if (parent == null || speciated) { // set some defaults, or perturb majorly
      for (int i = 0; i < inputWeights.length; i++) {
        inputWeights[i] += normal(0, 2);
      }

      for (int i = 0; i < outputWeights.length; i++) {
        outputWeights[i] += normal(0, 2);
        outputWeights2[i] += normal(0, 2);
      }

      for (int i = 0; i < inputBiases.length; i++) {
        inputBiases[i] += normal(0, 2);
        outputBiases[i] += normal(0, 2);
        outputBiases2[i] += normal(0, 2);
      }
    }

    if (!speciated) {      
      // perturb a few W&B
      final float SM_PERTURB = random(0, 0.01);
      for (int i = 0; i < this.species.adaptability; i++) {
        inputWeights[randInt(0, inputWeights.length - 1)] += normal(0, SM_PERTURB);
        inputBiases[randInt(0, inputBiases.length - 1)] += normal(0, SM_PERTURB);
        outputWeights[randInt(0, outputWeights.length - 1)] += normal(0, SM_PERTURB);
        outputBiases[randInt(0, outputBiases.length - 1)] += normal(0, SM_PERTURB);
        outputWeights2[randInt(0, outputWeights.length - 1)] += normal(0, SM_PERTURB);
        outputBiases2[randInt(0, outputBiases.length - 1)] += normal(0, SM_PERTURB);
      }
    }

    hp = 1; //((float) newModules.size()) / 2;
    //hp += random(hpMin, Math.min(maxHp, hpMax));
    this.requiredReplication = 12;

    if (speciated) { // prepend the primary food (which we only know after birthing)
      this.species.name = SUBSTANCE_LABELS[this.primaryFood].substring(0, 1) + "-" + this.species.name;
    }
    beingMap.put(id, this);
    this.species.addPopulation();
  }

  public String debugStatus() {
    return "Energy: " + storage[ENERGY] + " Food: " + storage[FOOD];
  }

  public void think(float[][][] grid, Being[][] beingGrid) {
    moved = true;
    int inputLayerIndex = 0;
    for (int i = 0; i < inputModules.size(); i++) {
      float input = inputModules.get(i).getInput(this, grid, beingGrid);
      if (listener != null) {
        listener.input(input);
      }
      for (int j = 0; j < outputModules.size(); j++) {
        hiddenLayer[j] += input * inputWeights[inputLayerIndex];
        inputLayerIndex++;
      }
    }
    for (int j = 0; j < outputModules.size(); j++) {
      hiddenLayer[j] = (float) Math.tanh(hiddenLayer[j] + inputBiases[j]);
      if (listener != null) {
        listener.hidden(hiddenLayer[j]);
      }
    }

    int hiddenLayerIndex = 0;
    for (int i = 0; i < outputModules.size(); i++) {
      float input = hiddenLayer[i];
      for (int j = 0; j < outputModules.size(); j++) {
        hiddenLayer2[j] += input * outputWeights[hiddenLayerIndex];
        hiddenLayerIndex++;
      }
    }
    for (int j = 0; j < outputModules.size(); j++) {
      hiddenLayer2[j] = (float) Math.tanh(hiddenLayer2[j]  + outputBiases[j]);
    }

    int outputLayerIndex = 0;
    for (int i = 0; i < outputModules.size(); i++) {
      float input = hiddenLayer2[i];
      for (int j = 0; j < outputModules.size(); j++) {
        outputLayer[j] += input * outputWeights2[outputLayerIndex];
        outputLayerIndex++;
      }
    }
    for (int j = 0; j < outputModules.size(); j++) {
      outputLayer[j] = (float) Math.tanh(outputLayer[j]  + outputBiases2[j]);
      if (listener != null) {
        listener.output(outputLayer[j]);
      }
    }
  }

  public void executeLifecycle(float[][][] grid, Being[][] beingGrid) {
    if (!moved) { // I haven't moved yet.
      int outputModuleIndex = 0;

      List<Module> activeModules = new ArrayList<Module>();
      List<Float> moduleInputs = new ArrayList<Float>(modules.size());
      for (Module mod : modules) {
        if (mod instanceof BinaryOutputModule) {
          float out = outputLayer[outputModuleIndex++];
          if (out > 0) {
            activeModules.add(mod);
            moduleInputs.add(out);
          }
        } else if (mod instanceof DataOutputModule) {
          float out = outputLayer[outputModuleIndex++];
          activeModules.add(mod);
          moduleInputs.add(out);
        } else {
          activeModules.add(mod);
          moduleInputs.add(1f);
        }
      }

      for (int i = activeModules.size() - 1; i >= 0; i--) {
        Module mod = activeModules.get(i);
        if (!mod.suffocate(this, grid, beingGrid)) break;
        if (!alive) return;
      }
      for (int i = activeModules.size() - 1; i >= 0; i--) {
        Module mod = activeModules.get(i);
        if (!mod.digest(this, grid, beingGrid)) break;
        if (!alive) return;
      }
      // post-digestion: don't store anything we can't.
      for (int i = 0; i < NUM_CHEMS - 1; i++) {
        store(i, 0);
      }

      for (int i = activeModules.size() - 1; i >= 0; i--) {
        Module mod = activeModules.get(i);
        if (!mod.respire(this, grid, beingGrid)) break;
        if (!alive) return;
      }

      boolean move = true;
      int beforeX = x;
      int beforeY = y;
      for (int i = activeModules.size() - 1; i >= 0; i--) {
        Module mod = activeModules.get(i);
        mod.absorb(this, grid, beingGrid);
        if (move) {
          move = mod.move(this, grid, beingGrid);
        }
        if (!alive) return;
      }
      if (beforeX == x && beforeY == y) { // can't reproduce/replicate/utility if you moved.
        for (int i = activeModules.size() - 1; i >= 0; i--) {
          Module mod = activeModules.get(i);
          if (!mod.reproduce(this, grid, beingGrid)) break;
          if (!alive) return;
        }
        if (!alive) return;

        for (int i = activeModules.size() - 1; i >= 0; i--) {
          Module mod = activeModules.get(i);
          if (!mod.replicate(this, grid, beingGrid)) break;
          if (!alive) return;
        }
        if (!alive) return;

        for (int i = activeModules.size() - 1; i >= 0; i--) {
          Module mod = activeModules.get(i);
          if (!mod.attack(this, grid, beingGrid)) break;
          if (!alive) return;
        }
        if (!alive) return;

        for (int i = activeModules.size() - 1; i >= 0; i--) {
          Module mod = activeModules.get(i);
          if (!mod.utility(this, grid, beingGrid)) break;
          if (!alive) return;
        }
      }

      if (!alive) return;
      age++;
      if (age > species.maxAge) {
        die(grid, beingGrid);
      }
    }
  }

  public boolean move(int toX, int toY, Being[][] beingGrid) {
    if (beingGrid[toX][toY] == null) {
      beingGrid[x][y] = null;
      beingGrid[toX][toY] = this;
      x = toX;
      y = toY;
      return true;
    }
    return false;
  }

  // returns damage done
  public float takeDamage(Being attacker, float hp, float[][][] grid, Being[][] bg) {
    if (!alive) {
      return 0;
    }
    for (Module mod : modules) {
      hp = mod.modifyDamage(attacker, this, hp, grid, bg);
    }
    float actualDamage = Math.max(0, Math.min(this.hp, hp));
    this.hp -= actualDamage;
    if (this.hp <= 0) {
      this.die(grid, bg);
    }
    return actualDamage;
  }

  public void die(float[][][] grid, Being[][] bg) {
    //println("killing " + x + ", " + y);
    if (!alive) return; // don't die twice

    alive = false;
    bg[x][y] = null;
    // everything in storage goes to the cell
    for (int i = 0; i < NUM_CHEMS - 1; i++) {
      addToGrid(x, y, i, storage[i] * random(0.9, 0.99));
    }

    this.species.subtractPopulation();
    beingMap.remove(id);
    //println(this.species.population + " left of " + this.species.name);
  }

  /**
   * Returns the amount stored (could be less than amt if we didn't have capacity)
   */
  public float store(int substance, float amt) {
    float starting = storage[substance];
    storage[substance] += amt;
    storage[substance] = Math.max(0, Math.min(storage[substance], storageCapacities[substance]));
    return storage[substance] - starting;
  }
}

class Perk {
}

class Gene {
  public final List<Module> modules = new ArrayList<Module>();
}

class Species implements Comparable<Species> {
  public final long id;
  public String name;
  public final List<Perk> perks = new ArrayList<Perk>();
  public final List<Gene> genes = new ArrayList<Gene>();
  private final List<Module> birthModules = new ArrayList<Module>();

  public int population = 0;
  public int minPopulation = 100;
  public int maxPopulation = 1;
  private color myColor = -1;
  private int myHash = -1;
  public final int generation;
  public final int primaryFood;
  public final int adaptability;
  public final float maxAge;

  public Species(Species parent, int primaryFood, long id, String name) {
    this.id = id;
    this.name = name;
    this.generation = (parent != null) ? (parent.generation + 1) : 1;
    this.primaryFood = primaryFood;
    this.adaptability = (parent == null) ? randInt(0, 10) : (parent.adaptability + randInt(-1, 1));
    this.maxAge = Math.min(120, normal(50, 5));
  }

  public List<Module> getBirthModules() {
    if (birthModules.size() == 0) {
      for (Gene g : genes) {
        birthModules.addAll(g.modules);
      }
    }
    return birthModules;
  }

  private void popMinMax() {
    if (population < minPopulation) {
      minPopulation = population;
    }
    if (population > maxPopulation) {
      maxPopulation = population;
    }
  }

  public int addPopulation() {
    population++;
    popMinMax();
    if (!this.equals(globalPopulation)) {
      globalPopulation.addPopulation();
    }
    return population;
  }

  public int subtractPopulation() {
    population--;
    popMinMax();
    if (!this.equals(globalPopulation)) {
      globalPopulation.subtractPopulation();
    }
    if (population <= 0) {
      speciesList.remove(this);
    }
    return population;
  }

  public color getColor() {
    if (myColor == -1) {
      myColor = color(randInt(0, 255), randInt(0, 255), randInt(0, 255));
    }
    return myColor;
  }

  public int compareTo(Species s) {
    return Integer.valueOf(s.population).compareTo(this.population);
  }

  public String getModuleDesc() {
    String ret = this.name + ": a" + adaptability + ": ";
    for (Gene g : genes) {
      for (Module m : g.modules) {
        ret += ((ret.equals("")) ? "" : ", ");
        ret += m.getName();
      }
    }
    return ret;
  }
}

class Substance {
  public final long id;
  public final String name;
  public float population = 0;
  public float minPopulation = Float.MAX_VALUE;
  public float maxPopulation = Float.MIN_VALUE;

  public Substance(long id, String name) {
    this.id = id;
    this.name = name;
  }

  public void popMinMax() {
    if (population < minPopulation) {
      minPopulation = population;
    }
    if (population > maxPopulation) {
      maxPopulation = population;
    }
  }

  public float addPopulation() {
    population++;
    popMinMax();
    return population;
  }

  public float subtractPopulation() {
    population--;
    popMinMax();
    return population;
  }
}

interface InputModule extends Module {
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid);
}

interface OutputModule extends Module {
}

/** Output module which accepts data. */
interface DataOutputModule extends OutputModule {
}

/** Output module which fires when input is > 0. */
interface BinaryOutputModule extends OutputModule {
}

/** Module which can't be removed by mutation. */
interface InherentModule extends Module {
}

interface Module {

  public String getName();
  public String getDescription();
  public String getShortDescription();

  public void birth(Being me);

  /** Called after all birth methods have been called. */
  public void postBirth(Being me);

  // if returns false, no more modules of this type should be fired.
  public boolean suffocate(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean digest(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean respire(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean absorb(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean replicate(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean reproduce(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean move(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean attack(Being me, float[][][] grid, Being[][] beingGrid);

  // if returns false, no more modules of this type should be fired.
  public boolean utility(Being me, float[][][] grid, Being[][] beingGrid);

  // -----------------
  // action-related methods:

  // returns modified damage (or hp if no modifier)
  public float modifyDamage(Being attacker, Being me, float hp, float[][][] grid, Being[][] beingGrid);

  // returns a mutated version of this same module, if applicable (minor mutation)
  public Module mutate(Being me);
}

class BaseModule implements Module {

  public String shortDesc;
  public String name;
  public String description;

  public BaseModule(String shortDesc, String name, String desc) {
    this.shortDesc = shortDesc;
    this.name = name;
    this.description = desc;
  }

  public String getName() {
    return name;
  }

  public String getDescription() {
    return description;
  }

  public String getShortDescription() {
    return shortDesc;
  }

  public void birth(Being me) {
  }

  public void postBirth(Being me) {
  }

  public boolean suffocate(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean digest(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean respire(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean absorb(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean replicate(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean reproduce(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean move(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean attack(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public boolean utility(Being me, float[][][] grid, Being[][] beingGrid) {
    return true;
  }
  public float modifyDamage(Being attacker, Being me, float hp, float[][][] grid, Being[][] beingGrid) {
    return hp;
  }
  public Module mutate(Being me) {
    return this;
  }

  public int hashCode() {
    return name.hashCode();
  }
}  

class StorageLevelSensor extends BaseModule implements InputModule {
  int substance;

  public StorageLevelSensor(int substance, String shortName, String longName, String desc) {
    super(shortName, longName, desc);
    this.substance = substance;
  }

  public StorageLevelSensor(int substance) {
    this(substance, SUBSTANCE_LABELS[substance].substring(0, 1) + " SS", SUBSTANCE_LABELS[substance] + " Storage Sensor", "Returns the current % " + SUBSTANCE_LABELS[substance] + " level.");
  }

  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    return map(me.storage[substance], 0, Math.max(me.storageCapacities[substance], 0.01), -1, 1, true);
  }
}

class FoodStorageSensor extends StorageLevelSensor {
  public FoodStorageSensor() {
    super(ENERGY, "FSS", "Primary Food Storage Sensor", "Returns the current % primary food level.");
  }

  public void postBirth(Being me) {
    this.substance = me.primaryFood;
  }
}

class HealthSensor extends BaseModule implements InputModule {
  public HealthSensor() {
    super("HS", "Health Sensor", "Returns the current % HP level.");
  }

  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    return map(me.hp, 0, me.maxHp + 0.00000001, -1, 1, true);
  }
}

class SubstanceSensor extends BaseModule implements InputModule {
  public final static int MAX_RANGE = 8;
  final float xStep;
  final float yStep;
  final int radius;
  int substance;

  protected SubstanceSensor(String shortName, String longName, String desc, float xStep, float yStep, int radius, int substance) {
    super(shortName, longName, desc);
    this.xStep = xStep;
    this.yStep = yStep;
    this.radius = radius;
    this.substance = substance;
  }

  public SubstanceSensor(float xStep, float yStep, int radius, int substance) {
    this(SUBSTANCE_LABELS[substance].substring(0, 1) + " S", SUBSTANCE_LABELS[substance] + " Sensor (" + df2.format(xStep) + "," + df2.format(yStep) + "," + radius + ")", "Returns the " + SUBSTANCE_LABELS[substance] + " level of the target square relative to the current square.", xStep, yStep, radius, substance);
  }

  public SubstanceSensor(int food) {
    this(random(-1, 1), random(-1, 1), randInt(1, MAX_RANGE), food);
  }

  public SubstanceSensor() {
    this(randInt(0, NUM_CHEMS - 2));
  }

  /**
   * Returns the ratio of the positive side to the negative side.
   */
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    float currentLevel = grid[me.x][me.y][substance];

    float left = 0;
    float right = 0;
    for (int i = 1; i <= radius; i++) {
      int x = (int) (me.x + (xStep * i));
      x = (x + GRID_WIDTH) % GRID_WIDTH;
      int y = (int) (me.y + (yStep * i));
      y = (y + GRID_HEIGHT) % GRID_HEIGHT;
      if (beingGrid[x][y] != null) { // can't "see past" other individuals
        break;
      }
      left += grid[x][y][substance];
    }
    for (int i = 1; i <= radius; i++) {
      int x = (int) (me.x + (-xStep * i));
      x = (x + GRID_WIDTH) % GRID_WIDTH;
      int y = (int) (me.y + (-yStep * i));
      y = (y + GRID_HEIGHT) % GRID_HEIGHT;
      if (beingGrid[x][y] != null) { // can't "see past" other individuals
        break;
      }
      right += grid[x][y][substance];
    }
    float ret;
    if (left + right == 0 || (left < currentLevel && right < currentLevel)) {
      ret = 0;
    }
    ret = (left - right) / (left + right);
    return ret;
  }

  public Module mutate(Being me) {
    return new SubstanceSensor();
  }
}

class PrimaryFoodSensor extends SubstanceSensor {

  public PrimaryFoodSensor() {
    this(Math.round(random(-1.49, 1.49)), Math.round(random(-1.49, 1.49)), randInt(1, SubstanceSensor.MAX_RANGE));
  }

  public PrimaryFoodSensor(float xStep, float yStep, int radius) {
    super("PFS", "Primary Food Sensor (" + df2.format(xStep) + "," + df2.format(yStep) + "," + radius + ")", "Returns the primary food level of the target square relative to the current square.", xStep, yStep, radius, 1);
  }

  public void postBirth(Being me) {
    this.substance = me.primaryFood;
  }

  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    return super.getInput(me, grid, beingGrid);
  }

  public Module mutate(Being me) {
    return new PrimaryFoodSensor(Math.round(random(-1.49, 1.49)), Math.round(random(-1.49, 1.49)), Math.min(SubstanceSensor.MAX_RANGE, (int)(radius * random(0.5, 1.5))));
  }
}

class PopulationSensor extends BaseModule implements InputModule {
  final float xStep;
  final float yStep;
  final int radius;
  final int food;

  /**
   * food is either -1 or the index of the food to be surveyed.
   */
  public PopulationSensor(float xStep, float yStep, int radius, int food) {
    super("p" + (food == -1 ? "Pop" : SUBSTANCE_LABELS[food]).substring(0, 1) + "S", (food == -1 ? "Pop" : SUBSTANCE_LABELS[food]) + " Sensor (" + df2.format(xStep) + "," + df2.format(yStep) + "," + radius + ")", "Returns the population level of the target vector.");
    this.xStep = xStep;
    this.yStep = yStep;
    this.radius = radius;
    this.food = food;
  }

  public PopulationSensor() {
    this(randInt(-1, 1), randInt(-1, 1), randInt(1, SubstanceSensor.MAX_RANGE), randInt(-1, NUM_CHEMS-2));
  }

  private int population(int x, int y) {
    return (beingGrid[x][y] != null && (this.food == -1 || this.food == beingGrid[x][y].species.primaryFood)) ? 1 : 0;
  }

  /**
   * Returns the ratio of the positive side to the negative side.
   */
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    float left = 0;
    float right = 0;
    for (int i = 0; i < radius; i++) {
      int x = (int) (me.x + (xStep * i));
      x = (x + GRID_WIDTH) % GRID_WIDTH;
      int y = (int) (me.y + (yStep * i));
      y = (y + GRID_HEIGHT) % GRID_HEIGHT;
      left += population(x, y);
    }
    for (int i = 0; i < radius; i++) {
      int x = (int) (me.x + (-xStep * i));
      x = (x + GRID_WIDTH) % GRID_WIDTH;
      int y = (int) (me.y + (-yStep * i));
      y = (y + GRID_HEIGHT) % GRID_HEIGHT;
      right += population(x, y);
    }
    float ret = 0;
    if (left + right == 0) {
      ret = 0;
    } else {
      ret = (left - right) / (left + right);
    }
    return ret;
  }

  public Module mutate(Being me) {
    return new PopulationSensor();
  }
}

/** Non-directional sensor of radius 1 detecting enemies. */
class AdjacentEnemySensor extends BaseModule implements InputModule {

  /**
   * food is either -1 or the index of the food to be surveyed.
   */
  public AdjacentEnemySensor() {
    super("AES", "Adjacent Enemy Sensor", "Returns number of enemies in radius 1.");
  }

  private int population(int x, int y, Being me) {
    return (beingGrid[x][y] != null && (me.species != beingGrid[x][y].species)) ? 1 : 0;
  }

  /**
   * Returns -1 to 1 based on number of adjacent enemies.
   */
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    float pop = 0;
    for (int i = -1; i <= 1; i++) {
      for (int j = -1; j<= 1; j++) {
        int x = (int) (me.x + i);
        x = (x + GRID_WIDTH) % GRID_WIDTH;
        int y = (int) (me.y + j);
        y = (y + GRID_HEIGHT) % GRID_HEIGHT;
        pop += population(x, y, me);
      }
    }
    return map(pop, 0, 8, -1, 1);
  }

  public Module mutate(Being me) {
    return this;
  }
}

/** Non-directional sensor of radius 1 detecting allies. */
class AdjacentAllySensor extends BaseModule implements InputModule {

  /**
   * food is either -1 or the index of the food to be surveyed.
   */
  public AdjacentAllySensor() {
    super("AAS", "Adjacent Ally Sensor", "Returns number of allies in radius 1.");
  }

  private int population(int x, int y, Being me) {
    return (beingGrid[x][y] != null && (me.species == beingGrid[x][y].species)) ? 1 : 0;
  }

  /**
   * Returns the ratio of the positive side to the negative side.
   */
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    float pop = 0;
    for (int i = -1; i <= 1; i++) {
      for (int j = -1; j <= 1; j++) {
        int x = (int) (me.x + i);
        x = (x + GRID_WIDTH) % GRID_WIDTH;
        int y = (int) (me.y + j);
        y = (y + GRID_HEIGHT) % GRID_HEIGHT;
        pop += population(x, y, me);
      }
    }
    if (pop == 1) {
      return 0;
    }
    return map(pop, 1, 9, -1, 1);
  }

  public Module mutate(Being me) {
    return this;
  }
}

class RespirationModule extends BaseModule implements InherentModule {
  final float pctSize;
  final float dmg;
  private boolean init = false;
  public RespirationModule(float pctSize, float dmg) {
    super("Resp", "Respiration " + df0.format(pctSize * 100) + "% / " + df1.format(dmg), "Consume " + df0.format(pctSize * 100) + "% gene size in energy or take " + df1.format(dmg) + " damage.");
    this.pctSize = pctSize;
    this.dmg = dmg;
  }

  public boolean respire(Being me, float[][][] grid, Being[][] bg) {
    me.respirationRequirement = (pctSize * me.respirationModifier * 0.35);
    me.starvationPenalty = dmg * me.respirationModifier;
    if (me.storage[ENERGY] >= me.respirationRequirement) { // can respire.
      //println("respiring for " + me.respirationRequirement);
      me.store(ENERGY, -1 * me.respirationRequirement);
    } else { // starving.
      //println("dying (penalty " + me.starvationPenalty + ", HP " + me.hp + ", energy " + me.storage[ENERGY] + ", food " + me.storage[FOOD] + ", requirement " + me.respirationRequirement + ")");
      me.takeDamage(null, me.starvationPenalty, grid, bg);
    }
    if (!me.alive) {
      return false;
    }
    return true;
  }
}

class RespirationModifierModule extends BaseModule {
  final float pctSize;
  public RespirationModifierModule(float pctSize) {
    super("RespMod", "Respiration Modifier " + df0.format(pctSize * 100) + "%", "Respiration is " + df0.format((1-pctSize) * 100) + "% more efficient and less damaging");
    this.pctSize = pctSize;
  }

  public void birth(Being me) {
    super.birth(me);
    me.respirationModifier *= pctSize;
  }
}

class BaseDigestModule extends BaseModule {
  public BaseDigestModule(String label, String desc) {
    super("Digest", label, desc);
  }
  public float[] intakes = new float[NUM_CHEMS]; // what it can absorb from the grid
  public float[] storageCapacities = new float[NUM_CHEMS]; // what it can store
  public float[] inputs = new float[NUM_CHEMS]; // what it can digest
  public float[] outputs = new float[NUM_CHEMS]; // what it will output internally upon digestion
  public float[] gridOutputs = new float[NUM_CHEMS]; // what it will output externally upon digestion

  public void birth(Being me) {
    super.birth(me);
    for (int i = 0; i < NUM_CHEMS; i++) {
      me.storageCapacities[i] += this.storageCapacities[i];
    }
  }

  @Override
    public boolean absorb(Being me, float[][][] grid, Being[][] beingGrid) {
    //println("ABSORB");
    for (int i = 0; i < NUM_CHEMS; i++) { // absorb chems that exist locally
      // absorb the lowest of what's available, what I can intake., and what I have left in storage.
      float toAbsorb = Math.min(Math.min(grid[me.x][me.y][i], intakes[i]), me.storageCapacities[i] - me.storage[i]);
      //if (me == listener.observed && i == me.primaryFood) {
      //  println(me.x + ", " + me.y + ": Absorbing " + toAbsorb + " from " + grid[me.x][me.y][i] + ", intakes " + intakes[i] + ", cap " + me.storageCapacities[i] + ", storage " + me.storage[i]);
      //}
      grid[me.x][me.y][i] -= toAbsorb;
      me.store(i, toAbsorb);
      //if (me == listener.observed && i == me.primaryFood) {
      //  println(me.x + ", " + me.y + ": Absorbed " + toAbsorb + " from " + grid[me.x][me.y][i] + ", intakes " + intakes[i] + ", cap " + me.storageCapacities[i] + ", storage " + me.storage[i]);
      //}
    }
    return true;
  }

  @Override
    public boolean digest(Being me, float[][][] grid, Being[][] beingGrid) {
    float pctDigest = 1;
    for (int i = 0; i < NUM_CHEMS; i++) {
      if (inputs[i] > 0 && me.storage[i] < inputs[i]) { // need an input we don't have all of.
        pctDigest = Math.min(pctDigest, me.storage[i] / inputs[i]);
        //if (me == listener.observed && (Math.abs(inputs[i]) > 0.1 || outputs[i] != 0)) {
        //  println("Inadequate input, pctDigest " + pctDigest);
        //}
      }
    }
    if (me.storageCapacities[ENERGY] - me.storage[ENERGY] < (outputs[ENERGY] * pctDigest)) { // we're not hungry.
      pctDigest = Math.min(pctDigest, (me.storageCapacities[ENERGY] - me.storage[ENERGY]) / outputs[ENERGY]);
      //if (me == listener.observed) {
      //  println("Not hungry, pctDigest " + pctDigest);
      //}
    }
    for (int i = 0; i < NUM_CHEMS; i++) {
      //if (me == listener.observed && (Math.abs(inputs[i]) > 0.1 || outputs[i] != 0)) {
      //  println("Digesting " + (outputs[i] - inputs[i]) * pctDigest + " " + SUBSTANCE_LABELS[i] + ", energy at " + me.storage[ENERGY] + " of " + me.storageCapacities[ENERGY]);
      //}
      me.store(i, (outputs[i] - inputs[i]) * pctDigest);
      //if (me == listener.observed && (Math.abs(inputs[i]) > 0.1 || outputs[i] != 0)) {
      //  println("Digested " + (outputs[i] - inputs[i]) * pctDigest + " " + SUBSTANCE_LABELS[i] + ", energy at " + me.storage[ENERGY] + " of " + me.storageCapacities[ENERGY]);
      //}
      // excrete in all surrounding squares
      for (int dx = -1; dx <=1; dx++) {
        for (int dy = -1; dy <=1; dy++) {
          addToGrid((me.x + dx + beingGrid.length) % (beingGrid.length), (me.y + dy + beingGrid[0].length) % (beingGrid[0].length), i, (gridOutputs[i] * pctDigest) / 9);
        }
      }
    }
    return true;
  }
}

class FoodDigestModule extends BaseDigestModule implements InherentModule {
  private final int primaryInput;
  private final float scalingFactor;
  private final float excretionRate;
  private final float storage;

  private boolean continueDigestion = true;

  public FoodDigestModule(int primaryInput, float scalingFactor, float excretionRate, float storage) {
    super(SUBSTANCE_LABELS[primaryInput] + " Processing " + df1.format(scalingFactor) + " / " + df1.format(excretionRate) + " / " + df1.format(storage), "Absorbs " + scalingFactor + " " + SUBSTANCE_LABELS[primaryInput] + ". Stores " + (10 * scalingFactor) + " " + SUBSTANCE_LABELS[primaryInput] + ". Digests " + scalingFactor + " " + SUBSTANCE_LABELS[primaryInput] + " into " + (10 * scalingFactor) + " energy and " + scalingFactor + " " + SUBSTANCE_LABELS[(primaryInput + 1) % (NUM_CHEMS - 1)] + ".");
    this.scalingFactor = scalingFactor;
    this.primaryInput = primaryInput;
    this.excretionRate = excretionRate;
    this.storage = storage;
    this.intakes[this.primaryInput] += scalingFactor;
    this.storageCapacities[this.primaryInput] += storage;
    this.inputs[this.primaryInput] += scalingFactor;
    this.outputs[ENERGY] += (12 * scalingFactor);
    this.gridOutputs[(this.primaryInput + 1) % (NUM_CHEMS - 1)] += (scalingFactor * excretionRate);
  }

  public void birth(Being me) {
    super.birth(me);
    if (me.primaryFood != primaryInput) {
      me.primaryFood = primaryInput;
      continueDigestion = false;
    }
  }

  @Override
    public boolean digest(Being me, float[][][] grid, Being[][] beingGrid) {
    super.digest(me, grid, beingGrid);
    return continueDigestion;
  }

  @Override
    public boolean absorb(Being me, float[][][] grid, Being[][] beingGrid) {
    super.absorb(me, grid, beingGrid);
    return continueDigestion;
  }

  public Module mutate(Being me) {
    return new FoodDigestModule(primaryInput, scalingFactor * random(0.9, 1.1), excretionRate * random(0.9, 1.1), storage * random(0.9, 1.1));
  }
}

class StorageModule extends BaseModule {
  private float[] capacities = new float[NUM_CHEMS];

  public StorageModule(int substance, float capacity) {
    super("Store", SUBSTANCE_LABELS[substance] + " Storage " + df1.format(capacity), "Stores " + df1.format(capacity) + " " + SUBSTANCE_LABELS[substance] + ".");
    this.capacities[substance] = capacity;
  }

  public void birth(Being me) {
    super.birth(me);
    for (int i = 0; i < capacities.length; i++) {
      me.storageCapacities[i] += this.capacities[i];
    }
  }
}

class MinorMutationModule extends BaseModule {
  private final float rate;

  public MinorMutationModule(float rateIncrease) {
    super("Min Mut", "Minor Mut " + df2.format(rateIncrease), "Increase minor mutation rate by " + rateIncrease);
    this.rate = rateIncrease;
  }

  public void birth(Being me) {
    super.birth(me);
    me.minorMutation += rate;
  }

  public Module mutate(Being me) {
    return new MinorMutationModule(rate * random(0.5, 1.5));
  }
}

class MajorMutationModule extends BaseModule {
  final float rate;

  public MajorMutationModule(float rate) {
    super("Maj Mut", "Major Mutation", "Change major mutation rate.");
    this.rate = rate;
  }

  public void birth(Being me) {
    super.birth(me);
    me.majorMutation *= rate;
  }

  public Module mutate(Being me) {
    return new MajorMutationModule(rate * random(0.5, 1.5));
  }
}

class ReplicateModule extends BaseModule implements BinaryOutputModule, InputModule, InherentModule {
  final float cost;

  public ReplicateModule() {
    this(random(2, 6));
  }

  public ReplicateModule(float cost) {
    super("Repl", "Replicate " + df1.format(cost), "Replicates 1 gene for " + df1.format(cost) + " energy.");
    this.cost = cost;
  }
  public boolean replicate(Being me, float[][][] grid, Being[][] beingGrid) {
    if (me.storage[ENERGY] >= cost) { // enough energy to replicate a gene
      me.store(ENERGY, -cost);
      if (me.replicationCount < me.requiredReplication) { //me.species.genes.size()) { // not fully replicated
        me.replicationCount++;
      }
    }
    return true;
  }
  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    return map(me.replicationCount, 0, me.requiredReplication, -1, 1, true);
  }
}

class HealthModule extends BaseModule implements InherentModule {
  final float hp;

  public HealthModule(float hp) {
    super("HP", "Health " + df1.format(hp), "Adds " + hp + " HP.");
    this.hp = hp;
  }

  public void birth(Being me) {
    super.birth(me);
    me.maxHp += this.hp;
  }
}

class AsexualReproductionModule extends BaseModule implements BinaryOutputModule, InputModule {
  private final float fertility;
  private final int maxAttempts;
  private final float hpToGive; // fixed number
  private final float resourcesToGive; // 0-1

  public AsexualReproductionModule(float chance, int maxAttempts, float hpToGive, float resourceShare) {
    super("Kid", "Asexual Reproduction " + df2.format(chance) + " / " + maxAttempts + " / " + hpToGive + " / " + df0.format(resourceShare * 100) + "%", "Reproduces asexually if all genes are replicated. Costs 1 energy (exertion) plus half remaining store of all substances (to offspring).");
    this.fertility = chance;
    this.maxAttempts = maxAttempts;
    this.hpToGive = hpToGive;
    this.resourcesToGive = resourceShare;
  }

  public float getInput(Being me, float[][][]grid, Being[][] beingGrid) {
    return map(me.offspringAttempts, 0, maxAttempts, -1, 1, true);
  }

  public boolean reproduce(Being me, float[][][] grid, Being[][] beingGrid) {
    float ENERGY_COST = 5;
    if (me.storage[ENERGY] < ENERGY_COST) { // tried too early; expend energy
      me.store(ENERGY, -ENERGY_COST / 2);
      return true;
    }
    if (me.replicationCount >= me.requiredReplication && random(1) <= fertility) { // reproduce!
      me.offspringAttempts++;
      if (me.replicationCount > 0) {
        me.replicationCount--;
      }
      // reproduction costs energy
      me.store(ENERGY, -ENERGY_COST);
      // check for best available space (most food).
      int xOffset = randInt(-1, 1);
      int yOffset = randInt(-1, 1);
      int destX = (me.x + xOffset + beingGrid.length) % beingGrid.length;
      int destY = (me.y + yOffset + beingGrid[0].length) % beingGrid[0].length;

      if (random(1) > 0.5) { // 50% of the time leave child on best food square
        float bestFood = -1;
        for (int dx = -1; dx <= 1; dx++) {
          for (int dy = -1; dy <= 1; dy++) {
            if (beingGrid[(me.x + dx + beingGrid.length) % beingGrid.length][(me.y + dy + beingGrid[0].length) % beingGrid[0].length] == null && grid[(me.x + dx + grid.length) % grid.length][(me.y + dy + grid[0].length) % grid[0].length][me.primaryFood] > bestFood) {
              bestFood = grid[(me.x + dx + grid.length) % grid.length][(me.y + dy + grid[0].length) % grid[0].length][me.primaryFood];
              destX = (me.x + dx + grid.length) % grid.length;
              destY = (me.y + dy + grid[0].length) % grid[0].length;
            }
          }
        }
      }

      if (me.offspringAttempts >= maxAttempts) { // too old, lose half HP
        me.takeDamage(null, me.hp / 2, grid, beingGrid);
        //me.die(grid, beingGrid);
      }
      if (beingGrid[destX][destY] == null && me.hp > hpToGive) { // empty, can reproduce.
        me.takeDamage(null, hpToGive, grid, beingGrid);
        Being child = new Being(me, me.species, me.primaryFood, destX, destY);
        beingGrid[destX][destY] = child;
        // give one HP and half storage (incl. HP) to child
        child.hp += hpToGive;

        for (int i = 0; i < NUM_CHEMS; i++) {
          float toGive = me.storage[i] * resourcesToGive;
          me.store(i, -toGive);
          child.store(i, toGive);
        }
      }
    }
    return false;
  }

  public Module mutate(Being me) {
    return new AsexualReproductionModule(random(fertility * 0.8, fertility * 1.2), maxAttempts + randInt(-1, 1), hpToGive * random(0.8, 1.2), Math.min(resourcesToGive * random(0.8, 1.2), 1));
  }
}

public MoveModule newMoveModule() {
  MoveModule ret;
  int xOff = randInt(-1, 1);
  int yOff = randInt(-1, 1);
  while (xOff == 0 && yOff == 0) {
    xOff = randInt(-1, 1);
    yOff = randInt(-1, 1);
  }
  ret = new MoveModule(xOff, yOff, random(0.01, 0.25), random(0.25, 2));
  return ret;
}

class MoveModule extends BaseModule implements BinaryOutputModule {
  private final float xOffset;
  private final float yOffset;
  private final float moveChance;
  private final float unitCost;

  public MoveModule(float xOffset, float yOffset, float movePct, float unitCost) {
    super("Move " + df1.format(movePct) + " " + df1.format(xOffset) + " " + df1.format(yOffset), "Move " + df1.format(movePct) + " @ " + df1.format(unitCost) + " (" + df1.format(xOffset) + ", " + df1.format(yOffset) + ")", "Moves in one direction (" + xOffset + ", " + yOffset + ")");
    //println("Moves in one direction (" + xOffset + ", " + yOffset + ")");
    this.xOffset = xOffset;
    this.yOffset = yOffset;
    this.moveChance = movePct;
    this.unitCost = unitCost;
  }

  public boolean move(Being me, float[][][] grid, Being[][] beingGrid) {
    if (random(1) > moveChance || me.storage[ENERGY] < unitCost) return true;

    int tgtX = 0;
    int tgtY = 0;
    float actualCost = 0;
    if (random(1) <= Math.abs(xOffset)) { // move in that dir
      tgtX = Math.round(xOffset);
      actualCost += (tgtX * unitCost);
    }
    if (random(1) <= Math.abs(yOffset)) { // move in that dir
      tgtY = Math.round(yOffset);
      actualCost += (tgtY * unitCost);
    }

    int destX = (me.x + tgtX + beingGrid.length) % (beingGrid.length);
    int destY = (me.y + tgtY + beingGrid[0].length) % (beingGrid[0].length);

    //println("Moving from " + me.x + ", " + me.y + " to " + destX + ", " + destY);

    if (destX == me.x && destY == me.y) { // not moving anywhere.
      return true;
    }

    if (me.move(destX, destY, beingGrid)) {
      me.store(ENERGY, -actualCost);
    } else { // tried to move into an occupied space, take damage as a penalty.
      me.takeDamage(null, 0.1, grid, beingGrid);
    }

    return true;
  }

  public Module mutate(Being me) {
    return newMoveModule();
  }
}

/** Takes damage for every neighbor above N. */
class SuffocateModule extends BaseModule implements InherentModule {
  final float maxNeighbors;
  final float dmg;

  public SuffocateModule(float maxNeighbors, float dmg) {
    super("Suff", "Suffocate " + df1.format(Math.max(0.1, dmg)) + "HP @ " + maxNeighbors, "Takes damage for every adjacent neighbor above " + maxNeighbors + ".");
    this.dmg = Math.max(0.1, dmg);
    this.maxNeighbors = maxNeighbors;
  }

  public boolean suffocate(Being me, float[][][] grid, Being[][] beingGrid) {
    int startX = constrain(me.x - 1, 0, beingGrid.length - 1);
    int endX = constrain(me.x + 1, 0, beingGrid.length - 1);
    int startY = constrain(me.y - 1, 0, beingGrid[0].length - 1);
    int endY = constrain(me.y + 1, 0, beingGrid[0].length - 1);

    int neighborCount = 0;

    for (int ix = startX; ix <= endX; ix++) {
      for (int iy = startY; iy <= endY; iy++) {
        if (beingGrid[ix][iy] != null & !(ix == me.x && iy == me.y)) { // neighbor (not me)
          neighborCount++;
        }
      }
    }

    for (int i = (int) maxNeighbors; i < neighborCount; i++) {
      if (me.alive) {
        me.takeDamage(null, dmg, grid, beingGrid);
      }
    }
    // don't run suffocate more than once
    return false;
  }

  public Module mutate(Being me) {
    return this;
    /* previous, but led to mutation to basically never suffocating:
     int modNeighbors = randInt(-1, 1);
     float dmgMult = random(0.95,1.1);
     return new SuffocateModule(Math.max(1, maxNeighbors + modNeighbors), dmg * dmgMult);
     */
  }
}

// paint an effect on the map
public void effect(int x, int y, int plane, int volume) {
  for (int xoff = -1; xoff <= 1; xoff++) {
    for (int yoff = -1; yoff <= 1; yoff++) {
      if (xoff == 0 && yoff == 0) { // add the volume to the center square
        effectGrid[(x + xoff + GRID_WIDTH) % GRID_WIDTH][(y + yoff + GRID_HEIGHT) % GRID_HEIGHT][plane] = volume;
      } else { // paint surrounding squares
        effectGrid[(x + xoff + GRID_WIDTH) % GRID_WIDTH][(y + yoff + GRID_HEIGHT) % GRID_HEIGHT][plane] = Math.min(effectGrid[(x + xoff + GRID_WIDTH) % GRID_WIDTH][(y + yoff + GRID_HEIGHT) % GRID_HEIGHT][plane] + 1, volume);
      }
    }
  }
}

class AttackModule extends BaseModule implements BinaryOutputModule {
  private final float toHit;
  private final float dmg;

  public AttackModule(float pctHit, float attack) {
    super("PvP", "Attack " + df1.format(attack) + "HP (" + df0.format(pctHit * 100) + "%)", "Attacks random neighbor for damage.");
    this.toHit = pctHit;
    this.dmg = Math.max(0, attack);
  }

  public boolean attack(Being me, float[][][] grid, Being[][] beingGrid) {
    int startX = constrain(me.x - 1, 0, beingGrid.length - 1);
    int endX = constrain(me.x + 1, 0, beingGrid.length - 1);
    int startY = constrain(me.y - 1, 0, beingGrid[0].length - 1);
    int endY = constrain(me.y + 1, 0, beingGrid[0].length - 1);

    boolean attacked = false;
    for (int x = startX; x <= endX; x++) {
      for (int y = startY; y <= endY; y++) {
        if (beingGrid[x][y] != null && (!beingGrid[x][y].species.equals(me.species))) { // found an enemy, attack.
          attacked = true;
          if (random(1) < toHit) { // hit
            float actualDmg = beingGrid[x][y].takeDamage(me, dmg, grid, beingGrid);
            //println("INFLICTED " + df1.format(actualDmg));
            me.store(ENERGY, actualDmg * 3); // gain energy (6 was way too high)

            effect(x, y, 0, 3); // blood

            return true;
          }
        }
      }
    }
    if (!attacked) { // waste some energy
      me.store(ENERGY, -dmg / 5);
    }      

    return true;
  }
}

class RegenModule extends BaseModule implements BinaryOutputModule {
  private final float regen;

  public RegenModule(float regen) {
    super("RG", "Regen " + df1.format(regen) + "HP", "Regenerates " + df1.format(regen) + "HP by burning " + df1.format(regen) + "energy.");
    this.regen = regen;
  }

  public RegenModule() {
    this(random(0.1, 3));
  }

  public boolean utility(Being me, float[][][] grid, Being[][] beingGrid) {
    if (me.maxHp - me.hp >= regen && me.storage[ENERGY] >= regen) {
      me.hp += regen;
      me.store(ENERGY, -regen);
    }

    return true;
  }
}

class ShareModule extends BaseModule implements BinaryOutputModule {
  private final float toShare;
  private final boolean shareToWeaker;
  protected int resource;

  public ShareModule(float toShare, int resource, boolean shareToWeaker, String shortName, String longName, String desc) {
    super(shortName, longName, desc);
    this.toShare = toShare;
    this.resource = resource;
    this.shareToWeaker = shareToWeaker;
  }

  public ShareModule(float toShare, int resource, boolean shareToWeaker) {
    this(toShare, resource, shareToWeaker, "s " + SUBSTANCE_LABELS[resource].substring(0, 1), "Share " + (shareToWeaker ? "Weaker " : "Stronger ") + df1.format(toShare) + " " + SUBSTANCE_LABELS[resource], "Shares resources with less-privileged ally.");
  }

  public boolean attack(Being me, float[][][] grid, Being[][] beingGrid) {
    int startX = constrain(me.x - 1, 0, beingGrid.length - 1);
    int endX = constrain(me.x + 1, 0, beingGrid.length - 1);
    int startY = constrain(me.y - 1, 0, beingGrid[0].length - 1);
    int endY = constrain(me.y + 1, 0, beingGrid[0].length - 1);

    for (int x = startX; x <= endX; x++) {
      for (int y = startY; y <= endY; y++) {
        if (beingGrid[x][y] != null && (beingGrid[x][y].species.equals(me.species)) && ((beingGrid[x][y].storage[resource] + toShare < me.storage[resource]) == shareToWeaker)) { // found an ally in need
          float actualShared = Math.min(me.storage[resource], toShare);
          actualShared = beingGrid[x][y].store(resource, actualShared);
          me.store(resource, -actualShared);
          effect(x, y, (resource == ENERGY) ? 2 : 1, 3); // show the share
          //println("SHARED " + df1.format(toShare));
          return true;
        }
      }
    }

    return true;
  }
}

class SharePrimaryFoodModule extends ShareModule {
  public SharePrimaryFoodModule(float toShare, boolean shareToWeaker) {
    super(toShare, FOOD, shareToWeaker, "s pf", "Share " + (shareToWeaker ? "Weaker " : "Stronger ") + df1.format(toShare) + " primary food", "Shares resources with less-privileged ally.");
  }
  public void postBirth(Being me) {
    this.resource = me.primaryFood;
  }
}

class DefendModule extends BaseModule {
  private float shield;

  public DefendModule(float shield) {
    super("Defend", "Defend " + df1.format(shield) + "HP", "Prevents damage from attacks.");
    this.shield = shield;
  }

  @Override
    public float modifyDamage(Being attacker, Being me, float hp, float[][][] grid, Being[][] bg) {
    if (attacker == null || attacker == me) {
      return hp;
    }

    float shielded = Math.min(shield, hp);
    shield -= shielded; // shield dies

    return hp - shielded;
  }
}

class Listener {
  final float[] inputs;
  final float[] hidden;
  final float[] outputs;
  final Being observed;
  int inputIndex = 0;
  int hiddenIndex = 0;
  int outputIndex = 0;
  Listener(Being being) {
    this.observed = being;
    being.listener = this;
    inputs = new float[being.inputModules.size()];
    hidden = new float[being.outputModules.size()];
    outputs = new float[being.outputModules.size()];
  }
  void input(float val) {
    this.inputs[inputIndex++ % this.inputs.length] = val;
  }
  void hidden(float val) {
    this.hidden[hiddenIndex++ % this.hidden.length] = val;
  }
  void output(float val) {
    this.outputs[outputIndex++ % this.outputs.length] = val;
  }
}
void settings() {
  size(SCREEN_WIDTH * GRID_UNIT, (GRID_HEIGHT * GRID_UNIT) + GRID_FOOTER);
}

private List<Species> speciesList = new ArrayList<Species>();
private List<Species> seedSpeciesList = new ArrayList<Species>();

private boolean shouldPopulate(int x, int y) {
  // landmasses (increase the / number to have larger continents, > number to have less land)
  return noise((float) x / 71, (float) y / 71) > 0.45;
  // cubes, evenly spaced
  //return (x / 40) % 2 == 0 && (y / 40) % 2 == 0;
  // spaced cubes, vertical bridges
  //return ((x / 45) % 3 != 1 && (y / 45) % 2 != 0) || ((x/8) % 12 == 1);
  // cubes, 1/3 spaced
  //return (x / 30) % 3 != 1 && (y / 30) % 3 != 1;
  // checkerboard
  //return (x / 25) % 2 == (y / 25) % 2;
  // checkerboard with diagonal gaps
  //return (x / 45) % 3 == (y / 45) % 3;
}

void populateMap(float[][][] grid, Being[][] beingGrid, float pctPopulate, int maxSpecies, boolean randomStart, boolean addChemicals, int food) {
  int currentSpeciesPopulation = 0;
  int usedSpecies = 0;
  int startX = randomStart ? randInt(0, GRID_WIDTH - 52) : 0;
  int startY = randomStart ? randInt(0, GRID_HEIGHT - 52) : 0;

  int endX = randomStart ? startX + 50 : GRID_WIDTH;
  int endY = randomStart ? startY + 50 : GRID_HEIGHT;

  Species currentSeedSpecies = speciate(speciesId++, food);

  for (int x = startX; x < endX; x++) {
    for (int y = startY; y < endY; y++) {
      if (addChemicals) {
        if (shouldPopulate(x, y)) {
          for (int c = 0; c < NUM_CHEMS - 1; c++) {
            float nx = noise((float) x/20, (float) y/20, (float) c * 7);
            if (nx > 0.5) {
              nx = 1;
            } else {
              nx = 0;
            }
            grid[x][y][c] = nx * 4; // how much of each chemical there is initially.
          }
        }
      }
      //println("SETUP2 " + noise((float) x, (float) y));

      if (random(1) > pctPopulate && beingGrid[x][y] == null) {
        //println("Adding at " + x + ", " + y);
        if (currentSpeciesPopulation > INITIAL_POPULATIONS) {
          currentSeedSpecies = speciate(speciesId++, food);
          currentSpeciesPopulation = 0;
          usedSpecies++;
        }
        Being b = new Being(null, currentSeedSpecies, currentSeedSpecies.primaryFood, x, y);
        // first generation gets free energy.
        b.storage[ENERGY] = b.storageCapacities[ENERGY];
        if (!speciesList.contains(currentSeedSpecies)) {
          speciesList.add(currentSeedSpecies);
        }
        beingGrid[x][y] = b;
        currentSpeciesPopulation++;
        if (usedSpecies >= maxSpecies) {
          return;
        }
      }
    }
  }
}

private Species speciate(int generation, int food) {
  Species species = new Species(null, food, System.currentTimeMillis(), SUBSTANCE_LABELS[food].substring(0, 1) + "-1-" + (generation+1));

  List<Module> allModules = new ArrayList<Module>();
  allModules.add(new FoodDigestModule(food, random(0.5, 3), random(0.99, 1.01), 0));
  allModules.add(new RespirationModule(random(0.8, 1), random(0.5, 2)));
  allModules.add(new StorageModule(ENERGY, normal(4, 1)));
  allModules.add(new StorageModule(food, normal(4, 1)));
  allModules.add(new ReplicateModule());
  allModules.add(new AsexualReproductionModule(random(0.1, 0.5), randInt(1, 10), randInt(1, 5), random(0, 1)));
  // was 1,8 for first suffocate range; this needs some work.
  allModules.add(new SuffocateModule(normal(5, 0.5), normal(2, 0.5)));
  allModules.add(new RegenModule());
  allModules.add(new HealthModule(normal(5, 1)));

  //allModules.add(new AdjacentAllySensor());
  //allModules.add(new AdjacentEnemySensor());
  //allModules.add(new AttackModule(random(0.1, 1), randInt(1, 5)));

  //int popsensors = randInt(0,1);
  //for (int i = 0; i < popsensors; i++) {
  //  allModules.add(new PopulationSensor(random(-1, 1), random(-1, 1), randInt(1, 20), randInt(0, 1) == 0 ? -1 : food));
  //}
  //int subsensors = randInt(0,2);
  //for (int i = 0; i < subsensors; i++) {
  //  allModules.add(new PrimaryFoodSensor());
  //}
  allModules.add(new StorageLevelSensor(ENERGY));
  allModules.add(new FoodStorageSensor());
  allModules.add(new HealthSensor());

  if (random(1) > 0.5) {
    allModules.add(newMoveModule());
  }

  for (Module mod : allModules) {
    Gene g = new Gene();
    g.modules.add(mod);
    species.genes.add(g);
  }
  return species;
}

void setup() {
  //frameRate(240);
  fill(#000000);
  rect(0, (GRID_HEIGHT+1) * GRID_UNIT, (GRID_WIDTH+100) * GRID_UNIT, ((GRID_HEIGHT + 100) * GRID_UNIT) + GRID_FOOTER - 1);

  f1 = createFont("MyriadPro-Light", 32);
  f2 = createFont("MyriadPro-Light", 20);
  f3 = createFont("MyriadPro-Light", 18);

  grid = new float[GRID_WIDTH][GRID_HEIGHT][NUM_CHEMS];
  effectGrid = new int[GRID_WIDTH][GRID_HEIGHT][3];
  beingGrid = new Being[GRID_WIDTH][GRID_HEIGHT];

  for (int c = 0; c < NUM_CHEMS; c++) {
    substanceList.add(new Substance(0, SUBSTANCE_LABELS[c]));
  }

  for (int i = 0; i < NUM_CHEMS - 1; i++) {
    populateMap(grid, beingGrid, 0.997, 100000, false, true, i);
  }
}

float map(float val, float from, float to, float mapFrom, float mapTo, boolean clamp) {
  float ret = map(val, from, to, mapFrom, mapTo);
  if (clamp) {
    return constrain(ret, min(mapFrom, mapTo), max(mapFrom, mapTo));
  } else {
    return ret;
  }
}

void mouseClicked() {
  if (mouseButton == LEFT) {
    viewMode = (viewMode + 1) % (1 + NUM_CHEMS);
    println("CLICK " + viewMode);
  }
  if (mouseButton == RIGHT) {
    showBeings = (showBeings + 1) % 3;
  }
}

int it = 0;
int[] iterations = new int[4];
float walkSpeed = 0.01; // pixels per iteration
float leftLimit = 0;
float rightLimit = 400;

long[] msTimings = new long[20];

void draw() {
  it++;
  final boolean substanceCensus = (it % 100 == 0);
  long startTime = System.currentTimeMillis();
  int timeInd = 0;
  
  if (paused) return;

  if (globalPopulation.population >= TARGET_POP_MIN) { // we're at target pop; slow down injection
    injectionRate -= 0.001;
  } else { // increase injection
    injectionRate += 0.001;
  }
  if (globalPopulation.population >= TARGET_POP_MAX) { // allow negative injection
    injectionRate = Math.min(Math.max(-0.01, injectionRate), 0.01);
  } else { // no negative injection
    injectionRate = Math.min(Math.max(0, injectionRate), 0.01);
  }
  int toInject = randInt(0, NUM_CHEMS - 2);
  iterations[toInject]++;

  int noiseSeed = randInt(0, 999999);

  walkSpeed += (injectionRate > 0) ? -0.001 : ((injectionRate < 0) ? 0.001 : 0); // go faster as population explodes, slower as it shrinks
  walkSpeed = constrain(walkSpeed, 0.01, 2);
  leftLimit += walkSpeed;
  rightLimit += walkSpeed;

  List<Being> allValues = new ArrayList<Being>(beingMap.values());
  ExecutorService newFixedThreadPool = Executors.newFixedThreadPool(8);
  for (final Being being : allValues) {
    newFixedThreadPool.execute(new Runnable() {
      public void run() {
        being.think(grid, beingGrid);
      }
    });
  }
  newFixedThreadPool.shutdown();

  try {
    newFixedThreadPool.awaitTermination(10000000, TimeUnit.SECONDS);
  } catch (InterruptedException ie) {}

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  for (Being being : allValues) {
    //println("Running " + being.id);
    if (listener == null || !listener.observed.alive || !listener.observed.species.equals(speciesList.get(0))) { // find a new being to observe
      if (being.species.equals(speciesList.get(0))) {
        listener = new Listener(being);
      }
    }
    //println(System.currentTimeMillis() + " Executing at " + x + ", " + y);
    //println(beingGrid[x][y].debugStatus());
    being.moved = false; // reset action for next time.
    if (being.hp <= 0 && beingMap.get(being.id) != null) {
      being.die(grid, beingGrid);
    } else {
      being.executeLifecycle(grid, beingGrid);
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  if (((injectionRate < -0.0000001 || injectionRate > 0.0000001) && nextMaxUpdate % 20 == 0) || LONG_WALK_MODE || nextMaxUpdate <= 0) { // go through the entire grid
    for (int x = 0; x < GRID_WIDTH; x++) {
      for (int y = 0; y < GRID_HEIGHT; y++) {
        // do stuff

        if (LONG_WALK_MODE) { // dynamic undulation mode
          float leftside = leftLimit % GRID_WIDTH;
          float rightside = rightLimit % GRID_WIDTH;
          if ((x > leftside && x < rightside) || (rightside < leftside && (x < rightside || x > leftside))) {
            if (beingGrid[x][y] == null) { // don't feed any existing organisms
              if (toInject != speciesList.get(0).primaryFood) { // feed the non-top-performing food best
                grid[x][y][toInject] = Math.max(grid[x][y][toInject] + 0.05, 5);
              } else { // don't choke out the top-performing food, just feed less
                grid[x][y][toInject] = Math.max(grid[x][y][toInject] + 0.02, 2);
              }
            }
          } else {
            grid[x][y][toInject] = Math.max(grid[x][y][toInject] * 0.9, 0);
          }
        } else { // "normal" fixed/injection mode
          if (injectionRate < 0) { // suck the life out across the board.
            if (shouldPopulate(x, y)) { // slight suck
              grid[x][y][toInject] = Math.max(0, grid[x][y][toInject] * (1 + (injectionRate * 20)));
            } else { // "sea", big suck
              grid[x][y][toInject] = Math.max(0, grid[x][y][toInject] * (0.75));
            }
          } else if (injectionRate > 0 && shouldPopulate(x, y)) {
            grid[x][y][toInject] = grid[x][y][toInject] + (injectionRate * 20 * noise(((float) x/20)+noiseSeed, ((float) y/20)+noiseSeed, ((float) toInject * 7)+noiseSeed));
          }
        }
      }
    }
    if (nextMaxUpdate <= 0) {
      nextMaxUpdate = 5000;
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  loadPixels();

  if (skipFrames > 0) {
    println("SKIPPING " + skipFrames--);
    return;
  }

  if (substanceCensus) {
    for (int zzz = 0; zzz < NUM_CHEMS; zzz++) {
      substanceList.get(zzz).population = 0;
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  for (int x = 0; x < GRID_WIDTH; x++) {
    for (int y = 0; y < GRID_HEIGHT; y++) {
      color col = color(0, 0, 0);
      if (substanceCensus) {
        for (int c = 0; c < NUM_CHEMS; c++) {
          substanceList.get(c).population += grid[x][y][c];
        }
      }
      Being beingToRender = null;

      // show foreground
      if (viewMode < 2) { // show all beings
        if (beingGrid[x][y] != null && showBeings != 2) {
          beingToRender = beingGrid[x][y];
        }
      } else {
        // overlay chemical consumers!
        if (beingGrid[x][y] != null && showBeings != 2 && beingGrid[x][y].primaryFood == (viewMode - 2 % NUM_CHEMS)) {
          beingToRender = beingGrid[x][y];
        }
      }

      if (showEffects && effectGrid[x][y][0] > 0) { // render blood
        col = color(Math.min((effectGrid[x][y][0] * 40) + 128, 255), 0, 0);
        effectGrid[x][y][0]--;
      } else if (showEffects && effectGrid[x][y][1] > 0) { // render sharing food (green)
        col = color(0, Math.min((effectGrid[x][y][0] * 40) + 128, 255), 0);
        effectGrid[x][y][1]--;
      } else if (showEffects && effectGrid[x][y][2] > 0) { // render sharing energy (yellow)
        col = color(Math.min((effectGrid[x][y][0] * 40) + 128, 255), Math.min((effectGrid[x][y][0] * 10) + 128, 255), 0);
        effectGrid[x][y][2]--;
      } else if (beingToRender == null) {
        // show background if applicable
        if (viewMode == 1) { // all substance BG
          // going to find other colors, based on substance.
          float here = 0;
          for (int i = 0; i < NUM_CHEMS - 1; i++) {
            here += grid[x][y][i];
          }
          float hereVal = map(here, 0.00000001, CPS * 4, 0, 255);
          col = color(hereVal, hereVal, hereVal);
        } else if (viewMode > 1) { // specific substance BG
          // going to find other colors, based on substance.
          float here = grid[x][y][viewMode - 2];
          float hereVal = (constrain(here, 0, CPS) / CPS) * 255;
          col = color(hereVal, hereVal, hereVal);
        }
      } else { // show being
        color bc = beingGrid[x][y].species.getColor();
        float health = beingGrid[x][y].hp == 0 ? 0 : Math.max(beingGrid[x][y].hp / beingGrid[x][y].maxHp, 0.5);
        if (showBeings == 0) { // show species color
          col = color(red(bc) * health, green(bc) * health, blue(bc) * health);
        } else { // same color for all species
          float hereVal = health * 255;
          col = color(hereVal, (hereVal / 3f + 50), (hereVal / 5f) + 50);
        }
        beingGrid[x][y].moved = false; // reset action for next time.
      }

      for (int tgtX = x * GRID_UNIT; tgtX < (x * GRID_UNIT) + GRID_UNIT; tgtX++) {
        for (int tgtY = y * GRID_UNIT; tgtY < (y * GRID_UNIT) + GRID_UNIT; tgtY++) {
          int pix = (tgtX + tgtY * width);
          pixels[pix] = col; // color of square.
        }
      }
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  if (substanceCensus) {
    for (int c = 0; c < NUM_CHEMS; c++) {
      substanceList.get(c).popMinMax();
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  updatePixels();
  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  
  translate(0, GRID_HEIGHT * GRID_UNIT);

  int meterPadding = 20;
  int meterWidth = 80;
  int meterPos = 0;

  drawMeter("Global", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding, meterWidth, globalPopulation.population, globalPopulation.minPopulation, globalPopulation.maxPopulation, color(255, 204, 0), #00AA00, color(255, 204, 0));
  meterPos++;

  if (populateFood != -1) { // let's make some babies
    for (int i = 0; i < 50; i++) {
      populateMap(grid, beingGrid, 0.99, 1, true, false, populateFood);
    }
    populateFood = -1;
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();

  // could be used for meters of species??
  Collections.sort(speciesList);

  int[] extantFood = new int[NUM_CHEMS - 1];
  for (int i = 0; i < speciesList.size(); i++) {
    Species s = speciesList.get(i);
    if (s.population > 1) {
      extantFood[s.primaryFood]++;
      if (meterPos <= (7 * GRID_UNIT)) { // only draw 7 biggest species
        drawMeter(s.name, ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding, meterWidth, s.population, s.minPopulation, s.maxPopulation, s.getColor(), s.getColor(), s.getColor());
        meterPos++;
      }
    }
  }

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();

  for (int f = 0; f < extantFood.length; f++) {
    if (extantFood[f] < 2) { // create new species of this food when we're the only species left.
      for (int i = 0; i < 200; i++) {
        populateMap(grid, beingGrid, 0.99, 1, true, false, f);
      }
    }
  }  

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();

  while (meterPos <= (7 * GRID_UNIT)) {
    drawMeter("", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding, meterWidth, 0, 0, 1, color(255, 204, 0), #00AA00, color(255, 204, 0));
    meterPos++;
  }

  meterPos = 0;
  float totalBiomass = 0;
  for (int i = 0; i < substanceList.size() - 1; i++) {
    Substance s = substanceList.get(i);
    if (s.population < substanceMin) {
      substanceMin = s.population;
    }
    if (s.population > substanceMax) {
      substanceMax = s.population;
    }
    totalBiomass += s.population;
    drawMeter(s.name, ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, s.population, substanceMin, substanceMax, color(255, 204, 0), #00AA00, color(255, 204, 0));
    meterPos++;
  }

  drawMeter("Biomass", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, totalBiomass / 4, substanceMin, substanceMax, color(255, 204, 0), #00AA00, color(255, 204, 0));
  meterPos++;

  drawMeter2dp("HP", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.observed.hp, 0, listener.observed.maxHp, #AA0000, color(255, 204, 0), #00AA00);
  meterPos++;
  drawMeter2dp("Food", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.observed.storage[listener.observed.primaryFood], 0, listener.observed.storageCapacities[listener.observed.primaryFood], #AA0000, color(255, 204, 0), #00AA00);
  meterPos++;
  drawMeter2dp("Energy", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.observed.storage[ENERGY], 0, listener.observed.storageCapacities[ENERGY], #AA0000, color(255, 204, 0), #00AA00);
  meterPos++;
  drawMeter("DNA", ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.observed.replicationCount, 0, listener.observed.requiredReplication, #AA0000, color(255, 204, 0), #00AA00);
  meterPos++;

  for (int i = 0; i < listener.outputs.length; i++) {
    drawMeter("o" + i + " " + listener.observed.outputModules.get(i).getShortDescription(), ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.outputs[i], df5.format(listener.outputs[i]), -1, 1, #AA0000, color(255, 204, 0), #00AA00);
    meterPos++;
  }

  for (int i = 0; i < listener.inputs.length; i++) {
    drawMeter("i" + i + " " + listener.observed.inputModules.get(i).getShortDescription(), ((meterWidth + meterPadding) * meterPos) + meterPadding, meterPadding + 150, meterWidth, listener.inputs[i], df5.format(listener.inputs[i]), -1, 1, #AA0000, color(255, 204, 0), #00AA00);
    meterPos++;
  }

  noStroke();
  fill(#000000);
  final int FOOTERTEXT = 325;
  final int FOOTERHEIGHT = 470;
  rect(meterPadding, FOOTERTEXT, (GRID_WIDTH * GRID_UNIT)-80, FOOTERHEIGHT);

  fill(#ffffff);
  textFont(f3);
  String label = "Life";
  if (viewMode > 1) {
    label = SUBSTANCE_LABELS[viewMode - 2];
  } else if (viewMode == 1) {
    label = "Resources";
  }

  text("View Mode: " + label + ", " + speciesList.size() + " species\nInjection Rate " + df5.format(injectionRate) + ", Walk speed " + walkSpeed + "\n" + ((speciesList.size() > 0) ? speciesList.get(0).getModuleDesc() : "") + "\n" + ((speciesList.size() > 1) ? speciesList.get(1).getModuleDesc() : "") + "\n" + ((speciesList.size() > 2) ? speciesList.get(2).getModuleDesc() : "") + "\n" + ((speciesList.size() > 3) ? speciesList.get(3).getModuleDesc() : ""), meterPadding, FOOTERTEXT, (GRID_WIDTH * GRID_UNIT) - 80, FOOTERHEIGHT);

  msTimings[timeInd++] += (System.currentTimeMillis() - startTime);
  startTime = System.currentTimeMillis();
  if (it % 1000 == 0) {
    for (int i = 0; i < timeInd; i++) {
      if (msTimings[i] > 0) {
        println("Timing " + i + ": " + msTimings[i]);
      }
    }
  }
  
  //println(frameRate);
}

void mousePressed() {
  // do something while mouse pressed
}

void mouseReleased() {
  // do something else after
}

float noise(String str, float custoff) {
  float val = ((float)(str.hashCode() % 1699)) + custoff;
  return noise(val);
}

color mapColor(float num, float from, float to, color c1, color c2) {
  return color(map(num, from, to, red(c1), red(c2), true), map(num, from, to, green(c1), green(c2), true), map(num, from, to, blue(c1), blue(c2), true));
}

public static float[][][] tripleCopy(float[][][] src) {
  float[][][] dst = new float[src.length][src[0].length][];
  for (int i = 0; i < src.length; i++) {
    for (int j = 0; j < src[0].length; j++) {
      dst[i][j] = Arrays.copyOf(src[i][j], src[i][j].length);
    }
  }
  return dst;
}

/**
 * Use this method when adding stuff to a grid square.
 */
void addToGrid(int x, int y, int substance, float qty) {
  grid[x][y][substance] += qty;

  if (grid[x][y][substance] > CPS) { // redistribute
    float redistPortion = (grid[x][y][substance] - CPS) / grid[x][y][substance];
    for (int i = Math.max(0, x - 1); i <= Math.min(x + 1, GRID_WIDTH - 1); i++) {
      for (int j = Math.max(0, y - 1); j <= Math.min(y + 1, GRID_HEIGHT - 1); j++) {
        float toMove = (redistPortion / 9) * grid[x][y][substance];
        grid[x][y][substance] -= toMove;
        grid[i][j][substance] += toMove;
      }
    }
  }
}

void drawMeter(String label, int x, int y, int mwidth, float val, float minVal, float maxVal, color colorBand1, color colorBand2, color colorBand3) {
  drawMeter(label, x, y, mwidth, val, df0.format(val), minVal, maxVal, colorBand1, colorBand2, colorBand3);
}

void drawMeter2dp(String label, int x, int y, int mwidth, float val, float minVal, float maxVal, color colorBand1, color colorBand2, color colorBand3) {
  drawMeter(label, x, y, mwidth, val, df2.format(val), minVal, maxVal, colorBand1, colorBand2, colorBand3);
}

void drawMeter(String label, int x, int y, int mwidth, float val, String valLabel, float minVal, float maxVal, color colorBand1, color colorBand2, color colorBand3) {
  pushMatrix();
  translate(x, y);

  // show 20 steps
  color col = #000000;
  if (val < ((maxVal - minVal) / 2) + minVal) { // bottom half
    col = mapColor(val, minVal - 0.0001, ((maxVal - minVal) / 2) + minVal, colorBand1, colorBand2);
  } else {
    col = mapColor(val, ((maxVal - minVal) / 2) + minVal - 0.0001, maxVal, colorBand2, colorBand3);
  }

  float to100 = map(val, minVal, maxVal, 2, 98, true);

  noStroke();
  stroke(#333333);
  fill(#333333);
  rect(0, 0, mwidth, 98 - to100);
  stroke(col);
  fill(col);
  rect(0, 99-to100, mwidth, to100);

  textFont(f2);

  noStroke();
  fill(#000000);
  rect(0, 100, mwidth, 40);

  fill(#ffffff);

  text(valLabel, 0, 100, mwidth, 40);
  text(label, 0, 115, mwidth, 40);


  popMatrix();
}

private float normal(float mean, float sdev) {
  return (randomGaussian() * sdev) + mean;
}

/**
 * Returns a random number between the min and max (inclusive).
 */
public static int randInt(int min, int max) {
  if (max == 0) {
    return 0;
  } else {
    return (int) r.nextInt(max - min + 1) + min;
  }
}
