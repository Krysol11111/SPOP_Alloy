/*
 * Adapted from Exercise A.1.11 on page 236 of
 * Software Abstractions, by Daniel Jackson
 *
 * In this exercise, you'll write some constraints about a simplified version
 * of the railway lines of the London Underground, or "tube". (You can find the
 * real thing at http://tube.tfl.gov.uk/.) There are three lines shown: the
 * Jubilee line running north to south from Stanmore; the Central line running
 * west to east to Epping; and the Circle line running clockwise through Baker
 * Street.
 *
 * A simplified portion of the tube is shown below
 *
 *               Stanmore
 *             x
 *             |
 *             | Baker Street
 *           - x -
 *         /   |   \
 *        /    |    \
 *       |     |     |         Epping
 *  -----------------|-------x
 *       |     |     |
 *        \    |    /
 *         \   |   /
 *           -----
 *             |
 *             |
 *
 * You are given the following relations:
 *
 *  - Station:
 *    the set of all stations
 *
 *  - JubileeStation, CentralStation, CircleStation:
 *    for each line, a subset of Station
 *
 *  - jubliee, central, circle:
 *    binary relations relating stations on each line to one another if they
 *    are directly connected
 *
 *  - Stanmore, BakerStreet, Epping
 *    singleton subsets of Station for individual stations
 *
 * Formalize each of the following statements using the Alloy logic in the
 * model as indicated below.
 *   a) named stations are on exactly the lines as shown in graphic
 *   b) no station (including those unnamed) is on all three lines
 *   c) the Circle line forms a circle
 *   d) Jubilee is a straight line starting at Stanmore
 *   e) there's a station between Stanmore and BakerStreet
 *   f) it is possible to travel from BakerStreet to Epping
 */

sig Station {}

sig JubileeStation in Station {
  jubilee: set JubileeStation
}

sig CentralStation in Station {
  central: set CentralStation
}

sig CircleStation in Station {
  circle: set CircleStation
}

one sig Stanmore, BakerStreet, Epping extends Station {}

fact {
  // write the corresponding constraint below each statement

  // a) named stations are on exactly the lines as shown in graphic
  all e:Epping | e in CentralStation and e not in JubileeStation and e not in CircleStation
  all s:Stanmore | s not in CentralStation and s in JubileeStation and s not in CircleStation
  all b:BakerStreet | b not in CentralStation and b in JubileeStation and b in CircleStation
  // b) no station (including those unnamed) is on all three lines
  no s:Station | s in CentralStation and s in JubileeStation and s in CircleStation
  // c) the Circle line forms a circle
  all disj c1,c2:CircleStation | #c1.circle = 2 and #c2.circle = 2 and ((c1 not in c2.circle and c2 not in c1.circle) or (c1 in c2.circle and c2 in c1.circle))
  all c:CircleStation | c not in c.circle
  // d) Jubilee is a straight line starting at Stanmore
  all disj j1,j2:JubileeStation | (j1 not in j2.jubilee and j2 not in j1.jubilee) or (j1 in j2.jubilee and j2 in j1.jubilee)
  all j:JubileeStation | j not in j.jubilee and #j.jubilee <= 2 and #j.jubilee >=1
  #{j:JubileeStation | #j.jubilee = 1} = 2
  all j1:{j:JubileeStation | j in Stanmore} |   #j1.jubilee = 1
  all disj j1,j2:{j:JubileeStation | #j.jubilee = 1} | j1 not in j2.jubilee //this makes #JubileeStation >= 3 unfortunately
  // e) there's a station between Stanmore and BakerStreet
  some disj j1,j2,j3:JubileeStation | j1 in Stanmore and j2 in BakerStreet and j1 in j3.jubilee and j3 in j1.jubilee and j2 in j3.jubilee and j3 in j2.jubilee
  // f) it is possible to travel from BakerStreet to Epping
  // i think e and f have swapped station names
}

pred show {}
run show for 6

// I can't think of how to prevent disjoining circles and circle forming for larger number of stations...
