enum LOC; % set of locations
LOC: base; % base location where information is collected
constraint assert(base = min(LOC),"base is not the first mentioned location\n");
int: n; % number of traps available
array[LOC] of int: wild; % amount of interesting wildlife at each location
array[LOC] of int: cost; % cost to setup trap at location, -ve means unavailable
constraint assert(cost[base] = 0, "Cost of base location is not 0\n");
array[LOC,LOC] of int: d; % distance from one location to another (symmetric)
constraint forall(l1, l2 in LOC where l1 <= l2)(assert(d[l1,l2] = d[l2,l1], "distance is not symmetric at \(l1) \(l2)\n"));
constraint forall(l in LOC)(assert(d[l,l] = 0, "self distance for \(l) is not zero\n"));
int: move; % movement distance of animals
int: link; % wireless link maximum communication distance;
int: mind; % mininum distance between two traps
int: opcost; % cost to maintain/operate camera trap
int: budget; % total budget for traps

set of int: PLACE0 = 0..n;
set of int: PLACE = 1..n;

array[PLACE0] of var LOC: x; % location where camera trap is placed (except 0)
constraint x[0] = base; % first chosen location must be base
%constraint forall(i in PLACE)(x[i] != base); % the remaining selections must not be base (part A)

array[LOC] of var bool: covered; % list of whether each location is covered by a trap
constraint forall(l in LOC)(covered[l] = exists(i in PLACE0 where x[i] != base)(d[l, x[i]] <= move)); % generate covered
constraint forall(i, j in PLACE where i < j /\ x[i] != base /\ x[j] != base)(d[x[i],x[j]] >= mind); % minimum distance between traps
constraint forall(l in x)(cost[l] >= 0); % cost can't be negative

constraint ((sum(i in PLACE where x[i] != base)(1) * opcost) 
           + sum(i in PLACE where x[i] != base)(cost[x[i]])) <= budget; % total cost must be less than budget
constraint forall(i in 1..n-1)(if x[i] = base then x[i+1] = base endif); % move dummies to end

array[PLACE] of var PLACE0: s; % location to send info (part C only)
%constraint forall(i in PLACE)(s[i] = 0); % set s to 0 forall
constraint forall(i in PLACE where x[i] = base)(s[i] = 0); % dummy locations always send to base
constraint forall(i in PLACE where x[i] != base)(s[i] < i); % tree structure must send to previous index 
constraint forall(i in PLACE where x[i] !=base)(d[x[i],x[s[i]]] <= link); % distance between trap and previous trap or base smaller than link

var int: total_wild = sum(l in LOC)(if covered[l] then wild[l] else 0 endif); % calculate total wildlife in traps

solve maximize total_wild;

%output [show(covered)];
%output [show(total_wild)];
%output [show(x)];
%output [show(s)];
