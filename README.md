# evolution

The greatest cellular automata ever created.

## Premise

This is an evolution simulator. Single-pixel organisms, called "beings", start with a simple set of genes and over time will mutate and become more complex. Each member of a species has a fixed set of genes, or "modules", which govern their abilities. Each being has its own neural network, inherited from its parent but which may evolve over time.

There are four basic food resources: food, waste, gas, and energy. Beings only eat one of the food types, and only mutate into new species with the same diet.

All beings have health (HP) and the ability to store their primary food and energy.

Food is digested into energy, which beings use for most actions. When a being runs out of energy, and fails to respire, it will take damage. Digestion also produces the next food resource as excrement: food eaters excrete waste; waste eaters excrete gas; gas eaters excrete air; and air eaters excrete food.

The game is a simulation, with no goal other than to watch your beings evolve and occasionally influence that evolution.

When a being reproduces, there is a chance it will mutate into a new species. New species may have one additional module, and/or lose one non-essential module.

The world settings govern how the world works, and how species evolve.

Commands:
*left-click*: change view mode (life / resources / food / waste / gas / air)
*right-click*: change view mode for beings only (visible / monochrome / invisible)
*e*: toggle visibility of events
*f*: speciate a bunch of food eating beings
*w*: speciate a bunch of waste eating beings
*g*: speciate a bunch of gas eating beings
*a*: speciate a bunch of air eating beings
*p*: pause
*space*: fast-forward 100 iterations
*c*: "spotlight colonization": each iteration, a single seed species will be placed on the highest value unconsumed resource. The seed species will have the same diet as the resource type. When in resource view, the highest value square of any resource will be seeded; when in a specific food view mode, only that food will be considered. Life view (with no visible resources) will not fire spotlight colonization.
