include "globals.mzn";
% nurse rostering project


% STAGE A data
enum NURSE;                                              % set of nurses to roster
enum SHIFT = { MORN, DAY, EVEN, NIGH, OFF };
int: nday;                                               % number of days for roster
set of int: DAYS = 1..nday; 
array[NURSE,DAYS] of bool: rostered_off;                 % nurse is guaranteed an off shift

% STAGE A constraints
constraint forall(n in NURSE, d in DAYS where rostered_off[n,d])
                 (sh[n,d] = OFF);                                                % nurses rostered off if guaranteed an off shift
constraint forall(d in 1..(nday-3), n in NURSE)((sh[n,d] = NIGH) 
              /\ (sh[n,d+1] = NIGH) /\ (sh[n,d+2] = NIGH) 
              -> (sh[n,d+3] != NIGH));                                           % no nurse is assigned more than 3 nights in a row
constraint forall(d in 1..(nday-2), n in NURSE)((sh[n,d] = OFF) 
              /\ (sh[n,d+1] = OFF) -> (sh[n,d+2] != OFF));                       % no nurse has more than 2 days off in a row
constraint forall(d in 1..(nday-1), n in NURSE)((sh[n,d] = NIGH 
               -> sh[n,d+1] != MORN /\ sh[n,d+1] != DAY) 
              /\ (sh[n,d] = EVEN -> sh[n,d+1] != MORN));                         % no morn or day shifts after night and no morn shifts after even
constraint forall(d in 2..(nday-1), n in NURSE)((sh[n,d] = DAY) 
             -> ((sh[n,d-1] = DAY) \/ (sh[n,d+1] = DAY)));                       % day shift on days other than last can't be isolated
constraint forall(n in NURSE)((sh[n,1] = DAY) -> (sh[n,2] = DAY));               % day shift on first day can't be isolated


% STAGE B data
int: maxweek;                                            % maximum working shifts in any 7 day period
int: maxnightfort;                                       % maximum night shifts in any 14 day period
int: minfort;                                            % minimum number of working shifts in any 14 day period
array[SHIFT,DAYS] of int: minshift;                      % minimum number of nurses rostered on each shift

% STAGE B constraints
constraint forall(d in DAYS)(global_cardinality_low_up([sh[n,d] | n in NURSE], 
           SHIFT, [minshift[s,d] | s in SHIFT], [card(NURSE) | s in SHIFT]));    % each shift per day has minimum nurses rostered
constraint forall(n in NURSE)(forall(d in 1..(nday-6))
          (sum([sh[n,d+i] != OFF | i in 0..6]) <= maxweek));                     % nurses not working more than max shifts in a week
constraint forall(n in NURSE)(forall(d in 1..(nday-13))(
          (sum([sh[n,d+i] != OFF | i in 0..13]) >= minfort) 
       /\ (sum([sh[n,d+i] = NIGH | i in 0..13]) <= maxnightfort)));              % nurses not working less than min or more than max nights in fortnight


% STAGE C data
array[NURSE] of int: shift_cost;                          % cost of nurse to work a shift

% STAGE C constraints
constraint total_cost = sum(n in NURSE, d in DAYS where sh[n,d] != OFF)
                           (shift_cost[n]);                                      % calculate total cost of rostered nurses


% STAGE D data
enum WARD;                                                % set of wards to roster
WARD: dummy;                                              % dummy ward
array[WARD,DAYS] of int: minward;                         % minimum number of nurses rostered to each ward
int: maxward;                                             % maximum number of wards any nurse can work in the roster period
array[NURSE,WARD] of var 0..1: worked;                    % boolean array if nurse worked in ward in roster period

% STAGE D constraints
constraint forall(d in DAYS)(assert(minward[dummy,d] = 0,                        "Dummy ward has non zero minimum on day \(d)\n"));
constraint forall(n in NURSE, d in DAYS)(sh[n,d] = OFF <-> wd[n,d] = dummy);     % rostered off then dummy ward and vice versa
constraint forall(d in DAYS)(global_cardinality_low_up([wd[n,d] | n in NURSE], 
           WARD, [minward[w,d] | w in WARD], [card(NURSE) | w in WARD]));        % minimum nurses assigned to each ward
constraint forall(n in NURSE, w in WARD)(worked[n,w] = 
             max([bool2int(wd[n,d] = w) | d in DAYS]));                          % fill "worked" array with 1 if worked 0 if not
constraint forall(n in NURSE)(sum(w in WARD)(worked[n,w]) <= maxward);           % nurses cant be assigned different wards more than maxward


% STAGE E data
enum SKILL;
SKILL: senior;                                             % which skill is senior
array[NURSE] of set of SKILL: skill;                       % skills that each nurse has
array[WARD] of set of SKILL: required;                     % particular skills for each ward
opt WARD: emergency;                                       % emergency ward if its being rostered
enum SLICE = { PREDAWN, AM, PM, LATE };
array[SHIFT] of set of SLICE: shift_slice = 
[{PREDAWN, AM}, {AM,PM}, {PM, LATE}, {LATE, PREDAWN}, {}]; % assign slice covered to shifts

% STAGE E constraints
%constraint forall(d in DAYS, w in WARD where required[w] != {})(
           %exists(n in NURSE)(wd[n,d] = w /\ (required[w] subset skill[n])));     % skilled nurse must be assigned to ward with required skill
%constraint forall(slice in SLICE, d in DAYS)(exists(n in NURSE, s in SHIFT)(
                  %slice in shift_slice[s] /\ senior in skill[n] /\ sh[n,d] = s)); % senior nurse rostered on every slice
%constraint if occurs(emergency) then forall(d in DAYS)(global_cardinality(
             %[sh[n,d] | n in NURSE where wd[n,d] = emergency], 
             %[MORN, DAY, EVEN, NIGH, OFF], [1, 1, 1, 1, 0], 
             %[card(NURSE), card(NURSE), card(NURSE), card(NURSE), card(NURSE)])) 
             %else true endif;                                                     % nurse must handover to next nurse


%%%% DECISIONS
array[NURSE,DAYS] of var SHIFT: sh; % shift for each nurse on each day
var 0..nday*sum(shift_cost): total_cost;
array[NURSE,DAYS] of var WARD: wd;  % ward rostered for each nurse
solve minimize total_cost;
