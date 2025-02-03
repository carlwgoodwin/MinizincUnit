include "globals.mzn";

% train scheduling
%%%%%%%%%%% Data %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
enum STOP;                             % set of stops
STOP: dstop;                           % dummy stop
array[STOP] of int: minimal_wait;      % minimum wait time at station 
array[STOP,STOP] of opt 0..infinity: travel_time; % travel time from each stop to another <> if not possible
array[STOP] of int: platform;          % number of platforms at station
enum STYPE = { ORDINARY, HUB, TERMINUS };
array[STOP] of STYPE: stype;           % type of STOP
array[STOP] of int: skip_cost;         % cost to skip the station (per service)
enum LINE = { SING, DOUB, QUAD, NONE };
array[STOP,STOP] of LINE: line;        % line type between stops
                  
enum ROUTE;                            % a sequence of STOPs
int: max_route_length;                 % longest route in number of stops
set of int: STOPNO = 1..max_route_length;         
array[ROUTE] of STOPNO: rlength;       % length of route
array[ROUTE,STOPNO] of STOP: route;    % route definitions; 
   
enum SERVICE;                          % the set of services to be scheduled                         
array[SERVICE] of ROUTE: sroute;       % the route for each service
int: makespan;                         % end of time considered;
set of int: TIME = 0..makespan;
TIME: min_sep;                         % min separation of services on the same line same direction
array[SERVICE] of TIME: service_start; % from when the service can start
array[SERVICE] of TIME: service_end;   % when the service ideally ends

enum ENGINE;                           % set of engines available
array[ENGINE] of STOP: start;          % start location for engines
enum SERVICEX = s(SERVICE) ++ e(ENGINE); 

%%%%%%%%%%% Constraints %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% STAGE A
constraint forall(s1 in SERVICE, s2 in STOPNO)((arrive[s1,s2] >= service_start[s1])   % no service arrives at first station before service start time
              /\ (wait[s1,s2] = depart[s1,s2] - arrive[s1,s2])                        % wait time is depart time minus arrive time
              /\ (stopped[s1,s2] = true -> (wait[s1,s2] >= minimal_wait[route[sroute[s1],s2]]))); % wait time when stopped is greater than minimal wait

constraint forall(s1 in SERVICE, s2 in 1..(max_route_length-1) where route[sroute[s1], s2] != dstop % arrive time at next stop is at least travel time
              /\ route[sroute[s1], s2+1] != dstop 
              /\ travel_time[route[sroute[s1], s2], route[sroute[s1], s2+1]] != <>)
(arrive[s1,s2+1] >= (depart[s1,s2] + travel_time[route[sroute[s1],s2],route[sroute[s1],s2+1]]));

constraint forall(s1 in SERVICE, s2 in 2..max_route_length where route[sroute[s1],s2] = dstop) 
                ((arrive[s1,s2] == depart[s1,s2-1])                                   % dummy stop arrival is depart from previous
              /\ (wait[s1,s2] = 0)                                                    % dummy stop wait time is 0
              /\ (depart[s1,s2] == arrive[s1,s2]));                                   % dummy stop depart time is arrival time

% STAGE B
constraint forall(st in STOP)(cumulative(
                 [arrive[s1,s2] | s1 in SERVICE, s2 in STOPNO where route[sroute[s1],s2] == st],  % trains waiting at a stop is not greater than platform
                 [wait[s1,s2] | s1 in SERVICE, s2 in STOPNO where route[sroute[s1],s2] == st], 
                 [1 | s1 in SERVICE, s2 in STOPNO where route[sroute[s1],s2] == st], platform[st]));

% STAGE C
constraint forall(s1 in SERVICE, s2 in STOPNO where stype[route[sroute[s1],s2]] != ORDINARY)
                 (stopped[s1,s2] = true); % set stopped to always true for not ordinary stops

var 0..infinity: delay_obj = sum(s1 in SERVICE)                                                   % calculate delay objective
(let {var STOPNO: last_stop = max([s2 | s2 in STOPNO where route[sroute[s1],s2] != dstop]); 
var int: actual_service_end = depart[s1, last_stop]} in abs(actual_service_end - service_end[s1]));

var 0..infinity: skip_obj = sum(s1 in SERVICE, s2 in STOPNO where stopped[s1,s2] = false)         % calculate skip objective
                               (skip_cost[route[sroute[s1],s2]]); 

% STAGE D  
constraint all_different(prev);

constraint forall(s in SERVICE, e in ENGINE)                                        % start location of engine matches first stop
(if prev[s] = e(e) then (start[e] = route[sroute[s],1] /\ engine[s] = e) endif);

constraint forall(s1,s2 in SERVICE)(if prev[s1] = s(s2)                                       % services linked through prev have the same engine
then (engine[s1] = engine[s2] /\ route[sroute[s2],rlength[sroute[s2]]] = route[sroute[s1],1]  % first stop of previous is the same as last stop of current
/\ depart[s2,rlength[sroute[s2]]] <= arrive[s1,1]) endif);                                    % end time of previous is before start time of current

% ASSERTIONS
constraint assert(forall(s in STOP)(minimal_wait[s] >= 0), "Negative minimal wait");
constraint assert(forall(s in STOP)(skip_cost[s] >= 0), "Negative skip cost");
constraint assert(forall(s in STOP where stype[s] != ORDINARY)(skip_cost[s] = 0), "Non-ordinary skip cost not zero");
constraint assert(forall(s in STOP where s != dstop)(platform[s] > 0), "Non-dummy platform not positive");
constraint assert(forall(s in STOP where s = dstop)(minimal_wait[s] = 0 /\ skip_cost[s] = 0 /\ platform[s] = 0), 
"Wait time, skip cost or platform number not zero for dummy stop");
constraint assert(forall(s in STOP)(travel_time[s,dstop] = 0 /\ travel_time[dstop,s] = 0), 
"Travel time to and from dummy stop not zero");
constraint assert(makespan >= 0, "End of time is negative");
constraint assert(forall(s in SERVICE)(service_end[s] > service_start[s]), "Service end before service start");
constraint assert(forall(s1,s2 in STOP)(line[s1,s2] == line[s2,s1]), "Line type not symmetric");
constraint assert(forall(s1,s2 in STOP)((travel_time[s1,s2] = 0 \/ travel_time[s1,s2] = <>) -> line[s1,s2] = NONE), 
"Line type not NONE when zero or absent travel time");
constraint assert(forall(r in ROUTE)(forall(s in (rlength[r]+1..max_route_length))
(route[r,s]=dstop) /\ forall(i in 1..rlength[r])(route[r,i] != dstop)), "Route length disagrees with definitions");
constraint assert(forall(r in ROUTE)(forall(s in 1..rlength[r]-1)
((route[r,s] != dstop /\ route[r,s+1] != dstop) -> 
(travel_time[route[r,s],route[r,s+1]] != <> /\ (travel_time[route[r,s],route[r,s+1]] != 0)))), 
"Consecutive non-dummy stops not connected");

%%%%%%%%%%% Decisions %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[SERVICE,STOPNO] of var TIME: arrive;    % arrive time at each stop
array[SERVICE,STOPNO] of var TIME: depart;    % depart time at each stop
array[SERVICE,STOPNO] of var TIME: wait;      % wait time at each stop
array[SERVICE,STOPNO] of var bool: stopped;   % which stops are actually made                                                           
var int: total_obj = delay_obj + skip_obj;    % calculate total objective
array[SERVICE] of var ENGINE: engine;         % which engine is used for each service
array[SERVICE] of var SERVICEX: prev;         % previous service or engine
solve minimize(total_obj);

                                                                                    
