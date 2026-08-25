/* ========================================================================== */
/* FLYSPECK - Computer Code                                           */
/*                                                                            */
/* Lemma: None                                                               */
/* Chapter: Tame Hypermap                     */
/* Author: Thomas C. Hales                                                    */
/* Date: created May 8, 2009, revised June 10, 2009        */
/* ========================================================================== */

/* MathProg model for the Kepler conjecture

Revised June 15, 2010. Many sets and parameters renamed for consistency.
Many of the inequalities are automatically generated from the formal specification.

The model starts with a tame hypermap, then breaks certain
quadrilaterals into two flats, certain pentagons into a flat+big4face
or into 2 flats+apiece, certain hexagons into flat+big5face.  The new
edges along cuts have length 2.52--sqrt8.

The sets std3, std4, std5, std6 index the
standard regions.  The other faces are faces of (V,E) obtained by
adding diagonals to E_std.  If a standard region with 5 or 6 darts
has no flat quarters, then it belongs to std56_flat_free.

The term apex refers to a distinguished dart on a face.

****************

The branching has the following types.

std3: 2-way split on a triangular standard region according to
  y4+y5+y6 <= 6.25.  node: 2-way split on a node according to yn <=
  2.18

std4: 5-way split on a standard quad, according to std4_diag3,
   apex_sup_flat one way, apex_sup_flat other way, flats one
   way, flats the other way.  In these first 4 cases, a new edge (the
   diagonal) is added to (V,E).  In std4_diag3, both diags are at
   least 3, but no new edge is added to (V,E).  

   The apex_sup_flat
   has both diags at least sqrt(8), and the shorter diagonal at most
   3.  The apex_sup_flat always splits along the shorter
   diagonal.  

   A flat has a diagonal at most sqrt(8).

std5: * 11-way split on std. pent, std56_flat_free, 5
(flat+big4face), 5 (flat+flat+Apiece).  In each case except the first,
one or two new diagonals are added to (V,E).

std6: * 6-way split on std. hex, std56_flat_free, 6
(flat+big5face).  Note that a big5face may have other flats within it,
that are not used in branching.  This is done to keep the branching on
hexagons to a minimum.

****************

Sets provided in the data file :
hypermap_id: a numerical identifier of the case.
card_node: the number of nodes. 
card_face: the number of faces in the hypermap (V,E). 
e_dart: quadruples (i1,i2,i3,j) where (i1,j) is a dart such that f(i1,j) = (i2,j), f(i2,j)=(i3,j).

std3, std4, std5, std6:  standard faces with 3,4,5,6 darts.  Includes special cases such as std4_diag3, std56_flat_free, 

std4_diag3: quads with both diags at least 3. It is the dart opposite the long edge.
std56_flat_free: pents, and hexes with no flat quarters.  

std3_big: standard triangles with y4+y5+y6>=6.25;
std3_small: standard triangles with y4+y5+y6<=6.25;

apex_sup_flat: apex of super flat triangulating a quad 
   with shorter diagonal at least sqrt8-3.
apex_flat: the apex darts of flat quarters.  It is the dart opposite the long edge.
apex_A: the apex darts of type A triangle in triangulation of pentagon
apex4: apex dart in complement of flat in pent, where the apex dart is defined as
  the dart x s.t. f x and f^2 x are the two darts along the long edge.
apex5: apex dart of complement of flat in hex, where the apex dart is defined as 
  in the apex4.  It is *not* the dart opposite the long edge.

d_edge_225_252: edge ye >= 2.25;
d_edge_200_225: edge ye <= 2.25;


node_218_252: node with yn >= 2.18;
node_236_252: node with yn >= 2.36;
node_218_236: node with yn >= 2.18 <= 2.36;
node_200_218: node with yn <= 2.18;

*/

param hypermap_id;
param pi := 3.1415926535897932;
param sol0 := 0.5512855984325308;
param tgt := 1.541;  # 1.54065864570856;
param sqrt8 := 2.8284271247461900;
param rho218 := 1.0607429578779386; # constant is rho(2.18).
param card_node 'number of nodes' >= 13, <= 15; 
param card_face 'number of faces' >= 0; 


# directed edge (i,j) identified with tail of arrow.
set node := 0..(card_node-1);
set face := 0..(card_face-1);
set e_dart 'extended dart' within node cross node cross node cross face;
set dart := setof {(i1,i2,i3,j) in e_dart} (i1,j);
set d_edge := dart;
set edge within dart cross dart := 
  setof{(i1,i2,i3,j1) in e_dart,(i0,i3,i2,j2) in e_dart}(i2,j1,i3,j2);

# face sets
set std3 within face; 
set std4 within face diff std3;  
set std5 within face diff (std3 union std4); 
set std6 within face diff (std3 union std4 union std5); 
set std56_flat_free within  std5 union std6;
set std4_diag3 within std4;
set std := std3 union std4 union std5 union std6; # all standard regions.
set non_std := face diff std;
set std3_big within std3;
set std3_small within std3;

# dart sets

set dart_std3:= {(i,j) in dart: j in std3};
set dart_std3_big := {(i,j) in dart: j in std3_big};
set dart_std3_small := {(i,j) in dart: j in std3_small};

set dart_std4:= {(i,j) in dart: j in std4};
set dart3:= setof {(i1,i2,i3,j1,k1,k2,k3,j2) in e_dart cross e_dart: 
   (j1 = j2) and (i2=k1) and (i3=k2) and (i1=k3)} (i1,j1);

# apex sets
set apex_flat within {(i,j) in dart : j in non_std};
set apex_sup_flat within {(i,j) in dart : j in non_std};
set apex_A within {(i,j) in dart : j in non_std};
set apex4 within {(i,j) in dart: j in non_std};  
set apex5 within {(i,j) in dart : j in non_std};  

# directed edges
set d_edge_225_252 within d_edge;
set d_edge_200_225 within d_edge;

# nodes.
set node_218_252 within node;
set node_236_252 within node_218_252;
set node_218_236 within node_218_252;
set node_200_218 within node;

## SPECIAL SETS OF dartS ##

# parts of darts of opposite nodes of apex_sup_flat:
set apex_sup_flat_pair := 
  setof {(i1,i2,i3,j1,i4,k3,k2,j2) in e_dart cross e_dart: 
  (i1,j1) in apex_sup_flat and (i4,j2) in apex_sup_flat and 
  (i2=k2) and (i3=k3)} (i1,j1,i4,j2);

# darts with opposite at least 2.52 others in [2,2.52].
set dartX :=  apex5 union
   setof{(i1,i2,i3,j) in e_dart: (i3,j) in apex5}(i1,j) union
   setof{(i1,i2,i3,j) in e_dart: (i3,j) in apex5}(i2,j) union
   {(i,j) in dart: j in std4 union std5 union std6};

# darts with opposite at least s8, others in [2,2.52].
set dartY := apex_sup_flat union apex4 union
    setof{(i1,i2,i3,j) in e_dart : (i2,j) in apex4}(i1,j);

# darts with opposite at least 3, others in [2,2.52].
set dart4_diag3 := {(i,j) in dart: j in std4_diag3};
set dart4_diag3_b := dart4_diag3;
# renamed Dec 12, 2010 from dart4_diag3_a.

set dart_std3_200_218 := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_200_218 and
   i2 in node_200_218 and
   i3 in node_200_218 and
    j in std3}(i2,j);

# l=low, m=midhigh, H=veryhigh, h=high (=m or H).
# w=wide, n=narrow, x=w or n.
# hll means y1:high,y2:low,y3:low

set apex_std3_hll := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_200_218 and
   i2 in node_218_252 and
   i3 in node_200_218 and
   j in std3}(i2,j);

set apex_std3_lhh := setof{(i1,i2,i3,j) in e_dart : 
   i1 in node_218_252 and
   i2 in node_200_218 and
   i3 in node_218_252 and
   j in std3}(i2,j);


#combined with dart_std3_mini, which does not have to be small!
set dart_std3_small_200_218 := dart_std3_200_218 inter dart_std3_small;

set dart_std3_big_200_218 := dart_std3_200_218 inter dart_std3_big;
set apex_std3_small_hll := apex_std3_hll inter dart_std3_small;

# basic variables
var azim{dart} >= 0, <= pi;
var azim2{dart3} >=0, <= pi;
var azim3{dart3} >=0, <= pi;
var ln{node} >= 0, <= 1;
var rhazim{dart} >=0, <= pi + sol0;
var rhazim2{dart3} >=0, <= pi + sol0;
var rhazim3{dart3} >=0, <= pi + sol0;
var yn{node} >= 2, <= 2.52;
var ye{d_edge} >= 2, <= 3;
var rho{node} >= 1, <= 1 + sol0/pi;
var sol{face} >= 0, <= 4.0*pi;
var tau{face} >= 0, <= tgt;
var y1{dart} >= 2, <=2.52;
var y2{dart} >=2, <=2.52;
var y3{dart} >=2, <=2.52;
var y4{dart3} >=2, <=3;
var y5{dart} >=2, <=3;
var y6{dart} >=2, <=3;
var y8{dart_std4} >= 2, <= 2.52;
var y9{dart_std4} >= 2, <= 2.52;

#report variables
var lnsum;
var ynsum;
var sqdeficit;

## objective
maximize objective: sum{i in node} ln[i];

## equality constraints

ynsum_def: sum{i in node} yn[i] = ynsum;
sqdeficit_def: tgt - sum{j in face} tau[j] = sqdeficit;
azim_sum{i in node}:  sum {(i,j) in dart} azim[i,j] = 2.0*pi;
rhazim_sum{i in node}:  sum {(i,j) in dart} rhazim[i,j] = 2.0*pi*rho[i];
sol_sum{j in face}: sum{(i,j) in dart} (azim[i,j] - pi) = sol[j] - 2.0*pi;
tau_sum{j in face}: sum{(i,j) in dart} (rhazim[i,j] - pi -sol0) = tau[j] - 2.0*(pi+sol0);
ln_def{i in node}: ln[i] = (2.52 - yn[i])/0.52;
rho_def{i in node}: rho[i] = (1 + sol0/pi) - ln[i] * sol0/pi;
edge_sym{(i1,j1,i2,j2) in edge}: ye[i1,j1] = ye[i2,j2];
y1_def{(i3,i1,i2,j) in e_dart}: y1[i1,j] = yn[i1];
y2_def{(i3,i1,i2,j) in e_dart}: y2[i1,j] = yn[i2];
y3_def{(i3,i1,i2,j) in e_dart}: y3[i1,j] = yn[i3];
y4_def{(i3,i1,i2,j) in e_dart :  (i1,j) in dart3}: y4[i1,j] = ye[i2,j];
y5_def{(i3,i1,i2,j) in e_dart}: y5[i1,j] = ye[i3,j];
y6_def{(i3,i1,i2,j) in e_dart}: y6[i1,j] = ye[i1,j];
y9_def{(i3,i1,i2,j) in e_dart : (i1,j) in dart_std4 }: y9[i1,j] = ye[i2,j];
y8_def{(i3,i1,i2,j) in e_dart: (i1,j) in dart_std4}: y8[i1,j] = y5[i3,j];
azim2c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: azim2[i2,j] = azim[i3,j];
azim3c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: azim3[i2,j] = azim[i1,j];
rhazim2c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: rhazim2[i2,j] = rhazim[i3,j];
rhazim3c{(i1,i2,i3,j) in e_dart : (i2,j) in dart3}: rhazim3[i2,j] = rhazim[i1,j];

## inequality constraints

RHA{(i,j) in dart}: rhazim[i,j] >= azim[i,j]*1.0;
RHB{(i,j) in dart}: rhazim[i,j] <= azim[i,j]*(1+sol0/pi);
RHBLO{(i,j) in dart: i in node_200_218}: rhazim[i,j] <= azim[i,j]*rho218;
RHBHI{(i,j) in dart: i in node_218_252}: rhazim[i,j] >= azim[i,j]*rho218;

## definitional inequalities
yy1 {(i,j) in dart_std3_big}:   y4[i,j]+y5[i,j]+y6[i,j] >= 6.25;
yy2 {(i,j) in dart_std3_small}:   y4[i,j]+y5[i,j]+y6[i,j] <= 6.25;
yy3 {i in node_218_252}: yn[i] >= 2.18;
yy4 {i in node_200_218}: yn[i] <= 2.18;
yy5 {i in node_236_252}: yn[i] >= 2.36;
yy6 {i in node_218_236}: yn[i] <= 2.36;
yy7 {i in node_218_236}: yn[i] >= 2.18;
yy8 {(i,j) in d_edge_225_252}: ye[i,j] >= 2.25;
yy9 {(i,j) in d_edge_200_225}: ye[i,j] <= 2.25;

# y bounds.
yy10 {(i,j) in dart : j in std}: ye[i,j] <= 2.52;
yy11 {(i,j) in apex_flat}: y4[i,j] >= 2.52;
yy12 {(i,j) in apex_sup_flat}: y4[i,j] >= sqrt8;
yy13 {(i,j) in apex_flat union apex_sup_flat}: y5[i,j] <= 2.52;
yy14 {(i,j) in apex_flat union apex_sup_flat}: y6[i,j] <= 2.52;
yy15 {(i,j) in dart3 diff apex_sup_flat}: y4[i,j] <= sqrt8;
yy16 {(i,j) in apex_A}: y4[i,j] <= 2.52; # others redun. via apex_flat
# {(i,j) in apex_sup_flat}: y4[i,j] <= 3; # redundant via ye.
# apex4 apex5: covered by neighbors unless there are 2.

# tau tame table D inequality (Main Estimate)

tau3{j in std3}: tau[j] >= 0;
tau4{j in std4}: tau[j] >= 0.206;
tau5{j in std5}: tau[j] >= 0.4819;
tau6{j in std6}: tau[j] >= 0.7120;

#old values:
#experiment May 15, 2011.  I reran and 0.7 and even 0.6 work fine.
#rerun on larger hex graph archive that uses the constant 0.7230.
#This works fine on the larger archive.  We could probably make it even smaller.
#tau6{j in std6}: tau[j] >= 0.7230;
#tau6{j in std6}: tau[j] >= 0.7578;

## AD HOC NONLINEAR INEQUALITIES

# secondary estimates:
# The following is precisely tame table D[4,1]:
#tauB5h 'ID[]' {(i,j) in apex5}: tau[j] >= 0.6548; 
#May 22, 2011 experiment:
tauB5h 'ID[]' {(i,j) in apex5}: tau[j] >= 0.616; 

# The next two appear as lemma ZHPXLTX in the flypaper.
# new values, Oct 22, 2010:
tauB4h 'ID[9620775909]' {(i,j) in apex4}: tau[j] >= 0.477;

# It is necessary, for example hypermap_id "207710175290" needs it (barely).
tau5h 'ID[9620775909-5]' {j in std5 inter std56_flat_free}: tau[j] >= 0.616;

perimZ 'ID[5691615370]' {(i1,i2,i3,j) in e_dart : j in std4_diag3}:
  y5[i1,j] + y6[i1,j] + y5[i3,j] + y6[i3,j] >= 8.472;

# constant 7.99 changed, Oct 20, 2010 so that it isn't sharp.
yapex_sup_flat 'ID[8673686234]' {(i1,j1,i2,j2) in apex_sup_flat_pair}:
   (y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2]-7.99) >= 2.75*(y4[i1,j1]-sqrt8);

# this one based on fact that diag of apex_sup_flat is shorter than the crossdiag.
# y4[i1,j1] is the diag, which is shorter than the cross diag. 
# By monotonicity of dih in opposite edge length, this may be substituted in.
# checked 2010-06-23.
# derived from 1085358243,
# which also appears in body.mod in a simpler form on domain apex_sup_flat
crossdiag 'ID[1085358243]+' 
   {(i1,i,i3,j1,k1,k2,k3,j2) in e_dart cross e_dart :
     i = k3 and i3 = k2 and (i1,j1,k1,j2) in apex_sup_flat_pair}:
  (azim[i,j1]+azim[i,j2]) - 1.903 - 0.4*(y1[i,j1] - 2)
  +0.49688*(y2[i,j2]+y3[i,j1]+y5[i,j1]+y6[i,j2]-8)
   -(y4[i1,j1]-sqrt8) >= 0;

## DEPRECATED AD HOC NONLINEAR INEQUALITIES:

# constant -0.22 changed from -0.24 on Oct 20, 2010
# It now holds on each sup flat separately.
# It is now autogenerated, so it has been commented out here.

#tausf3 'ID[5451229371]'  {(i1,j1,i2,j2) in apex_sup_flat_pair}:
# tau[j1]+tau[j2]  - 0.22
#    -0.14132*(y1[i1,j1]+ y2[i1,j1] + y3[i1,j1] + y1[i2,j2] - 8)
#    -0.38*(y5[i1,j1]+y6[i1,j1]+y5[i2,j2]+y6[i2,j2] -8) >= 0;

#old values:
#tauB4h 'ID[deprecated]' {(i,j) in apex4}: tau[j] >= 0.492;
#tau5h 'ID[deprecated]' {j in std5 inter std56_flat_free}: tau[j] >= 0.751;
# Old parameter values (changed May 18, 2011 after checking it all goes through):
# tau5h 'ID[deprecated]' {j in std5 inter std56_flat_free}: tau[j] >= 0.696;

# Commented out Oct 21, 2010. Not needed.
# tau6h 'ID[deprecated]' {j in std6 inter std56_flat_free}: tau[j] >= 0.91;

## END OF AD HOC NONLINEAR INEQUALITIES


# final dart sets.

set apex_flat_hll := setof {(i1,i,i3,j) in e_dart : i1 in node_200_218 and i in node_218_252 and  i3 in node_200_218 and (i,j) in apex_flat} (i,j);

set dart_mll_w := setof  {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 and (i,j) in apex_std3_hll and i in node_218_236} (i,j);

set dart_mll_n := setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_200_225 and (i,j) in apex_std3_hll and i in node_218_236} (i,j);

set dart_Hll_n :=  setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_200_225 and (i,j) in apex_std3_hll and i in node_236_252} (i,j);

set dart_Hll_w :=  setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 and (i,j) in apex_std3_hll and i in node_236_252} (i,j);

set apexf4 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex4} (i2,j);
set apexff4 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex4} (i3,j);
set apexf5 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex5} (i2,j);
set apexff5 := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex5} (i3,j);
set apexfA := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex_A} (i2,j);
set apexffA := setof {(i1,i2,i3,j) in e_dart: (i1,j) in apex_A} (i3,j);

# dart sets added Aug 1--5, 2010.  

set dart_std3_lw  :=  
   setof   {(i,i2,i3,j) in e_dart :   (i2,j) in d_edge_225_252 
     and (i,j) in dart_std3_big 
     and i in node_200_218}  (i,j);

# bug corrected May 10, 2011.
set dart_std3_mini := dart_std3_small_200_218 union 
   setof {(i1,i2,i3,j) in e_dart: (i1,j) in d_edge_200_225 
     and      (i2,j) in d_edge_200_225 and (i3,j) in d_edge_200_225 
     and i1 in node_200_218 
     and i2 in node_200_218 and i3 in node_200_218
     and j in std3 } (i1,j);

set apex_flat_l := {(i,j) in apex_flat : i in node_200_218 };

set apex_flat_h :=  {(i,j) in apex_flat : i in node_218_252 };

set apex_std3_lll_xww := 
  setof {(i,i2,i3,j) in e_dart : (i,j) in d_edge_225_252 
    and (i3,j) in d_edge_225_252
    and (i,j) in dart_std3_200_218 } (i,j);

set apex_std3_lll_wxx := 
    setof {(i,i2,i3,j) in e_dart : (i2,j) in d_edge_225_252 
    and (i,j) in dart_std3_200_218 } (i,j);

# Put auto generated body here.




 
# File automatically generated from nonlinear inequality list via lpstring().


ineq32 'ID[3137600529]' 
  { (i,j) in apex_flat_h } : 
  (((azim2[i,j]) + 0.0042) - (0.868174 + (((-0.701906) * ((-2.25) + y1[i,j])) + ((0.136514 * ((-2.) + y2[i,j])) + (((-0.209239) * ((-2.18) + y3[i,j])) + (((-0.493373) * ((-2.65) + y4[i,j])) + ((0.537385 * ((-2.) + y5[i,j])) + (0.0187672 * ((-2.2) + y6[i,j]))))))))) >= 0.0;


ineq33 'ID[6284721194]' 
  { (i,j) in apex_std3_hll } : 
  (((azim2[i,j]) + 0.0011) - (0.957661 + (((-0.250506) * ((-2.36) + y1[i,j])) + ((0.145114 * ((-2.1) + y2[i,j])) + (((-0.0549376) * ((-2.1) + y3[i,j])) + (((-0.0384445) * ((-2.45) + y4[i,j])) + ((0.5275 * ((-2.) + y5[i,j])) + (0.118819 * ((-2.45) + y6[i,j]))))))))) >= 0.0;


ineq34 'ID[9185711902]' 
  { (i,j) in apex_std3_hll } : 
  (((-(azim3[i,j])) + 0.0116) - ((-1.30119) + ((0.392915 * ((-2.36) + y1[i,j])) + ((0.142563 * ((-2.1) + y2[i,j])) + (((-0.258747) * ((-2.1) + y3[i,j])) + ((0.417088 * ((-2.45) + y4[i,j])) + (((-0.0606764) * ((-2.) + y5[i,j])) + ((-0.637966) * ((-2.45) + y6[i,j]))))))))) >= 0.0;


ineq35 'ID[6725783616]' 
  { (i,j) in apex_flat } : 
  (((azim3[i,j]) + 0.0046) - (0.88473 + (((-0.443946) * ((-2.36) + y1[i,j])) + (((-0.244711) * ((-2.1) + y2[i,j])) + ((0.205592 * ((-2.1) + y3[i,j])) + (((-0.739126) * ((-2.55) + y4[i,j])) + (((-0.127198) * ((-2.1) + y5[i,j])) + (0.61582 * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq36 'ID[1248932983]' 
  { (i,j) in apex_std3_lhh } : 
  (((-(azim2[i,j])) + 0.0059) - ((-1.33909) + ((0.0724529 * ((-2.) + y1[i,j])) + (((-0.486824) * ((-2.18) + y2[i,j])) + ((0.317329 * ((-2.18) + y3[i,j])) + (((-0.00479451) * ((-2.) + y4[i,j])) + (((-0.751179) * ((-2.25) + y5[i,j])) + (0.350857 * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq37 'ID[1836408787]' 
  { (i,j) in apex_std3_lhh } : 
  (((azim[i,j]) + 0.0012) - (1.01332 + ((0.148615 * ((-2.) + y1[i,j])) + (((-0.379006) * ((-2.18) + y2[i,j])) + (((-0.379441) * ((-2.18) + y3[i,j])) + ((0.583676 * ((-2.) + y4[i,j])) + (((-0.184708) * ((-2.25) + y5[i,j])) + ((-0.18471) * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq38 'ID[5943578801]' 
  { (i,j) in apex_sup_flat } : 
  (((azim2[i,j]) + 0.0047) - (0.936544 + (((-0.636113) * ((-2.1) + y1[i,j])) + ((0.140759 * ((-2.1) + y2[i,j])) + (((-0.0771734) * ((-2.3) + y3[i,j])) + (((-1.29068) * ((-2.82843) + y4[i,j])) + ((0.591328 * ((-2.1) + y5[i,j])) + ((-0.0521775) * ((-2.1) + y6[i,j]))))))))) >= 0.0;


ineq39 'ID[2763799127]' 
  { (i,j) in apex_sup_flat } : 
  (((-(azim3[i,j])) + 0.0076) - ((-0.956317) + ((0.419124 * ((-2.) + y1[i,j])) + (((-0.0753922) * ((-2.) + y2[i,j])) + (((-0.252307) * ((-2.) + y3[i,j])) + ((0.5 * ((-2.82843) + y4[i,j])) + (((-0.246082) * ((-2.) + y5[i,j])) + ((-0.788717) * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq40 'ID[4306175952]' 
  { (i,j) in dart_mll_n } : 
  (((azim2[i,j]) + 0.0035) - (1.05036 + (((-0.222178) * ((-2.18) + y1[i,j])) + ((0.132628 * ((-2.) + y2[i,j])) + (((-0.219284) * ((-2.) + y3[i,j])) + ((0.00563427 * ((-2.25) + y4[i,j])) + ((0.59096 * ((-2.) + y5[i,j])) + ((-0.0771574) * ((-2.52) + y6[i,j]))))))))) >= 0.0;


ineq41 'ID[2923748598]' 
  { (i,j) in dart_mll_n } : 
  (((-(azim[i,j])) + 0.0083) - ((-1.29912) + (((-0.284457) * ((-2.18) + y1[i,j])) + ((0.337354 * ((-2.) + y2[i,j])) + ((0.186287 * ((-2.) + y3[i,j])) + (((-0.645382) * ((-2.25) + y4[i,j])) + ((0.367671 * ((-2.52) + y5[i,j])) + (0.0536051 * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq42 'ID[6410081357]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((-(azim3[i,j])) + 0.0087) - ((-1.18616) + ((0.436647 * ((-2.18) + y1[i,j])) + ((0.032258 * ((-2.) + y2[i,j])) + (((-0.289629) * ((-2.) + y3[i,j])) + ((0.397053 * ((-2.52) + y4[i,j])) + (((-0.0210289) * ((-2.) + y5[i,j])) + ((-0.683341) * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq43 'ID[7316455966]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((azim2[i,j]) + 0.005) - (1.02005 + (((-0.256494) * ((-2.18) + y1[i,j])) + ((0.121497 * ((-2.) + y2[i,j])) + (((-0.256494) * ((-2.) + y3[i,j])) + (((-0.0116869) * ((-2.52) + y4[i,j])) + ((0.598233 * ((-2.) + y5[i,j])) + (0.0187672 * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq44 'ID[3425739813]' 
  { (i,j) in apex_flat } : 
  (((-(azim[i,j])) + 0.0011) - ((-1.67609) + (((-0.506322) * ((-2.18) + y1[i,j])) + ((0.212075 * ((-2.1) + y2[i,j])) + ((0.230669 * ((-2.1) + y3[i,j])) + (((-1.28579) * ((-2.52) + y4[i,j])) + ((0.249199 * ((-2.) + y5[i,j])) + (0.193545 * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq45 'ID[5756588587]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((azim2[i,j]) + 0.0025) - (1.16613 + (((-0.296776) * ((-2.) + y1[i,j])) + ((0.208935 * ((-2.) + y2[i,j])) + (((-0.196313) * ((-2.) + y3[i,j])) + (((-0.360575) * ((-2.25) + y4[i,j])) + ((0.652861 * ((-2.) + y5[i,j])) + ((-0.218063) * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq46 'ID[4222324842]' 
  { (i,j) in apex_std3_lll_xww } : 
  (((azim[i,j]) + 0.0071) - (1.09969 + ((0.146345 * ((-2.) + y1[i,j])) + (((-0.160538) * ((-2.) + y2[i,j])) + (((-0.151698) * ((-2.14) + y3[i,j])) + ((0.61314 * ((-2.) + y4[i,j])) + (((-0.236149) * ((-2.25) + y5[i,j])) + ((-0.242043) * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq47 'ID[9641946727]' 
  { (i,j) in apex_flat_l } : 
  (((azim2[i,j]) + 0.0071) - (0.98362 + (((-0.264094) * ((-2.18) + y1[i,j])) + ((0.149308 * ((-2.18) + y2[i,j])) + (((-0.312683) * ((-2.) + y3[i,j])) + (((-0.282792) * ((-2.65) + y4[i,j])) + ((0.581552 * ((-2.) + y5[i,j])) + (0.143669 * ((-2.3) + y6[i,j]))))))))) >= 0.0;


ineq48 'ID[2390583444]' 
  { (i,j) in dart_std3_mini } : 
  (((azim[i,j]) + 0.0012) - (1.08627 + ((0.159149 * ((-2.) + y1[i,j])) + (((-0.198496) * ((-2.1) + y2[i,j])) + (((-0.199306) * ((-2.1) + y3[i,j])) + ((0.590083 * ((-2.) + y4[i,j])) + (((-0.0888111) * ((-2.25) + y5[i,j])) + ((-0.0881846) * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq49 'ID[7291663656]' 
  { (i,j) in apex_flat } : 
  (((azim2[i,j]) + 0.0009) - (0.947391 + (((-0.637397) * ((-2.) + y1[i,j])) + ((0.120003 * ((-2.) + y2[i,j])) + (((-0.100814) * ((-2.3) + y3[i,j])) + (((-0.302956) * ((-2.65) + y4[i,j])) + ((0.547359 * ((-2.) + y5[i,j])) + ((-0.157745) * ((-2.2) + y6[i,j]))))))))) >= 0.0;


ineq50 'ID[6987934000]' 
  { (i,j) in dart_mll_w } : 
  (((azim2[i,j]) + 0.0042) - (0.952682 + (((-0.268837) * ((-2.36) + y1[i,j])) + ((0.130607 * ((-2.) + y2[i,j])) + (((-0.168729) * ((-2.) + y3[i,j])) + (((-0.0831764) * ((-2.52) + y4[i,j])) + ((0.580152 * ((-2.) + y5[i,j])) + (0.0656612 * ((-2.25) + y6[i,j]))))))))) >= 0.0;


ineq51 'ID[7819193535]' 
  { (i,j) in dart_std3_lw } : 
  (((azim2[i,j]) + 0.0011) - (1.16613 + (((-0.296776) * ((-2.) + y1[i,j])) + ((0.208935 * ((-2.) + y2[i,j])) + (((-0.243302) * ((-2.) + y3[i,j])) + (((-0.360575) * ((-2.25) + y4[i,j])) + ((0.636205 * ((-2.) + y5[i,j])) + ((-0.295156) * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq52 'ID[8384511215]' 
  { (i,j) in apex_flat } : 
  (((azim2[i,j]) + 0.0015) - (0.913186 + (((-0.390288) * ((-2.) + y1[i,j])) + ((0.115895 * ((-2.) + y2[i,j])) + ((0.164805 * ((-2.52) + y3[i,j])) + (((-0.271329) * ((-2.82843) + y4[i,j])) + ((0.584817 * ((-2.) + y5[i,j])) + ((-0.170218) * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq53 'ID[4750199435]' 
  { (i,j) in apex_flat } : 
  (((-(azim2[i,j])) + 0.0031) - ((-1.08346) + ((0.288794 * ((-2.) + y1[i,j])) + (((-0.292829) * ((-2.) + y2[i,j])) + ((0.036457 * ((-2.) + y3[i,j])) + ((0.348796 * ((-2.52) + y4[i,j])) + (((-0.762602) * ((-2.) + y5[i,j])) + ((-0.112679) * ((-2.) + y6[i,j]))))))))) >= 0.0;


ineq54 'ID[1894886027]' 
  { (i,j) in dart_Hll_w } : 
  ((1. * (azim2[i,j])) - (1.0494 + (((-0.401543) * (y1[i,j] - 2.36)) + ((0.207551 * (y2[i,j] - 2.)) + (((-0.0294227) * (y3[i,j] - 2.)) + (((-0.494954) * (y4[i,j] - 2.25)) + ((0.605453 * (y5[i,j] - 2.)) + ((-0.156385) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq55 'ID[5835568093]' 
  { (i,j) in dart_Hll_n } : 
  ((1. * (azim2[i,j])) - (1.0494 + (((-0.404131) * (y1[i,j] - 2.36)) + ((0.212119 * (y2[i,j] - 2.)) + (((-0.0402827) * (y3[i,j] - 2.)) + (((-0.299046) * (y4[i,j] - 2.25)) + ((0.643273 * (y5[i,j] - 2.)) + ((-0.266118) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq56 'ID[4002562507]' 
  { (i,j) in dart_mll_n } : 
  ((1. * (azim2[i,j])) - (1.0494 + (((-0.29013) * (y1[i,j] - 2.36)) + ((0.215328 * (y2[i,j] - 2.)) + (((-0.0715511) * (y3[i,j] - 2.)) + (((-0.267157) * (y4[i,j] - 2.25)) + ((0.650269 * (y5[i,j] - 2.)) + ((-0.295198) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq57 'ID[7409690040]' 
  { (i,j) in dart_mll_w } : 
  ((1. * (azim2[i,j])) - (1.0494 + (((-0.297823) * (y1[i,j] - 2.36)) + ((0.215328 * (y2[i,j] - 2.)) + (((-0.0792439) * (y3[i,j] - 2.)) + (((-0.422674) * (y4[i,j] - 2.25)) + ((0.647416 * (y5[i,j] - 2.)) + ((-0.207561) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq58 'ID[9925287433]' 
  { (i,j) in dart_Hll_w } : 
  (((-1.) * (azim[i,j])) - ((-1.542) + (((-0.490439) * (y1[i,j] - 2.36)) + ((0.321849 * (y2[i,j] - 2.)) + ((0.320956 * (y3[i,j] - 2.)) + (((-1.00902) * (y4[i,j] - 2.25)) + ((0.240709 * (y5[i,j] - 2.)) + (0.218081 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq59 'ID[4841020453]' 
  { (i,j) in dart_Hll_n } : 
  (((-1.) * (azim[i,j])) - ((-1.542) + (((-0.490439) * (y1[i,j] - 2.36)) + ((0.318125 * (y2[i,j] - 2.)) + ((0.32468 * (y3[i,j] - 2.)) + (((-0.740079) * (y4[i,j] - 2.25)) + ((0.178868 * (y5[i,j] - 2.)) + (0.205819 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq60 'ID[3139693500]' 
  { (i,j) in dart_mll_n } : 
  (((-1.) * (azim[i,j])) - ((-1.542) + (((-0.346773) * (y1[i,j] - 2.36)) + ((0.300751 * (y2[i,j] - 2.)) + ((0.300751 * (y3[i,j] - 2.)) + (((-0.702567) * (y4[i,j] - 2.25)) + ((0.172726 * (y5[i,j] - 2.)) + (0.172727 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq61 'ID[3872614111]' 
  { (i,j) in dart_mll_w } : 
  (((-1.) * (azim[i,j])) - ((-1.542) + (((-0.362519) * (y1[i,j] - 2.36)) + ((0.298691 * (y2[i,j] - 2.)) + ((0.287065 * (y3[i,j] - 2.)) + (((-0.920785) * (y4[i,j] - 2.25)) + ((0.190917 * (y5[i,j] - 2.)) + (0.219132 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq62 'ID[4041673283]' 
  { (i,j) in apex_std3_small_hll } : 
  (((-1.) * (azim2[i,j])) - ((-1.1864) + ((0.20758 * (y1[i,j] - 2.18)) + (((-0.236153) * (y2[i,j] - 2.)) + ((0.14172 * (y3[i,j] - 2.)) + ((0.263109 * (y4[i,j] - 2.)) + (((-0.737003) * (y5[i,j] - 2.)) + (0.12047 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq63 'ID[1284543870]' 
  { (i,j) in apex_std3_small_hll } : 
  ((1. * (azim2[i,j])) - (1.185 + (((-0.372262) * (y1[i,j] - 2.18)) + ((0.214849 * (y2[i,j] - 2.)) + (((-0.163775) * (y3[i,j] - 2.)) + (((-0.293508) * (y4[i,j] - 2.)) + ((0.656172 * (y5[i,j] - 2.)) + ((-0.267157) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq64 'ID[6619134733]' 
  { (i,j) in apex_std3_small_hll } : 
  (((-1.) * (azim[i,j])) - ((-1.27799) + (((-0.439002) * (y1[i,j] - 2.18)) + ((0.229466 * (y2[i,j] - 2.)) + ((0.229466 * (y3[i,j] - 2.)) + (((-0.771733) * (y4[i,j] - 2.)) + ((0.208429 * (y5[i,j] - 2.)) + (0.208429 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq65 'ID[8657368829]' 
  { (i,j) in apex_std3_small_hll } : 
  ((1. * (azim[i,j])) - (1.277 + ((0.273298 * (y1[i,j] - 2.18)) + (((-0.273853) * (y2[i,j] - 2.)) + (((-0.273853) * (y3[i,j] - 2.)) + ((0.708818 * (y4[i,j] - 2.)) + (((-0.313988) * (y5[i,j] - 2.)) + ((-0.313988) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq66 'ID[7743522046]' 
  { (i,j) in apex_std3_hll } : 
  (((-1.) * (azim2[i,j])) - ((-1.1865) + ((0.20758 * (y1[i,j] - 2.18)) + (((-0.236153) * (y2[i,j] - 2.)) + ((0.14172 * (y3[i,j] - 2.)) + ((0.263834 * (y4[i,j] - 2.)) + (((-0.771203) * (y5[i,j] - 2.)) + (0.0457292 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq67 'ID[5298513205]' 
  { (i,j) in apex_std3_hll } : 
  ((1. * (azim2[i,j])) - (1.185 + (((-0.302913) * (y1[i,j] - 2.18)) + ((0.214849 * (y2[i,j] - 2.)) + (((-0.163775) * (y3[i,j] - 2.)) + (((-0.443449) * (y4[i,j] - 2.)) + ((0.67364 * (y5[i,j] - 2.)) + ((-0.314532) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq68 'ID[3636849632]' 
  { (i,j) in apex_std3_hll } : 
  ((1. * (tau[j])) - (0.0345 + ((0.185545 * (y1[i,j] - 2.18)) + ((0.193139 * (y2[i,j] - 2.)) + ((0.193139 * (y3[i,j] - 2.)) + ((0.170148 * (y4[i,j] - 2.)) + ((0.13195 * (y5[i,j] - 2.)) + (0.13195 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq69 'ID[6836427086]' 
  { (i,j) in apex_std3_hll } : 
  (((-1.) * (azim[i,j])) - ((-1.27799) + (((-0.356217) * (y1[i,j] - 2.18)) + ((0.229466 * (y2[i,j] - 2.)) + ((0.229466 * (y3[i,j] - 2.)) + (((-0.949067) * (y4[i,j] - 2.)) + ((0.172726 * (y5[i,j] - 2.)) + (0.172726 * (y6[i,j] - 2.))))))))) >= 0.0;


ineq70 'ID[2151506422]' 
  { (i,j) in apex_std3_hll } : 
  ((1. * (azim[i,j])) - (1.2777 + ((0.281 * (y1[i,j] - 2.18)) + (((-0.278364) * (y2[i,j] - 2.)) + (((-0.278364) * (y3[i,j] - 2.)) + ((0.7117 * (y4[i,j] - 2.)) + (((-0.34336) * (y5[i,j] - 2.)) + ((-0.34336) * (y6[i,j] - 2.))))))))) >= 0.0;


ineq71 'ID[181212899 5]' 
  { (i,j) in apexff5 } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y3[i,j] - 2.)) + (((0.57 * (y2[i,j] - 2.)) - (0.745 * (2.52 - 2.52))) + ((0.268 * (y6[i,j] - 2.)) + (0.385 * (y5[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq72 'ID[181212899 4]' 
  { (i,j) in apexf5 } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y2[i,j] - 2.)) + (((0.57 * (y3[i,j] - 2.)) - (0.745 * (2.52 - 2.52))) + ((0.268 * (y5[i,j] - 2.)) + (0.385 * (y6[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq73 'ID[181212899 3]' 
  { (i,j) in apexff4 } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y3[i,j] - 2.)) + (((0.57 * (y2[i,j] - 2.)) - (0.745 * ((sqrt8) - 2.52))) + ((0.268 * (y6[i,j] - 2.)) + (0.385 * (y5[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq74 'ID[181212899 2]' 
  { (i,j) in apexf4 } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y2[i,j] - 2.)) + (((0.57 * (y3[i,j] - 2.)) - (0.745 * ((sqrt8) - 2.52))) + ((0.268 * (y5[i,j] - 2.)) + (0.385 * (y6[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq75 'ID[181212899 1]' 
  { (i,j) in apexfA } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y3[i,j] - 2.)) + (((0.57 * (y2[i,j] - 2.)) - (0.745 * (y4[i,j] - 2.52))) + ((0.268 * (y6[i,j] - 2.)) + (0.385 * (y5[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq76 'ID[181212899 0]' 
  { (i,j) in apexffA } : 
  (((((azim[i,j]) - 1.448) - (0.266 * (y1[i,j] - 2.))) + ((0.295 * (y2[i,j] - 2.)) + (((0.57 * (y3[i,j] - 2.)) - (0.745 * (y4[i,j] - 2.52))) + ((0.268 * (y5[i,j] - 2.)) + (0.385 * (y6[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq77 'ID[8611785756]' 
  { (i,j) in dart_std3_big_200_218 } : 
  ((((sol[j]) - 0.589) + ((0.24 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.)))) - (0.16 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.25)))))) - 0.) >= 0.0;


ineq78 'ID[8282573160]' 
  { (i,j) in apex_flat_hll } : 
  (((((((tau[j]) - 0.1413) - (0.214 * (y1[i,j] - 2.18))) - (0.1259 * (y2[i,j] + (y3[i,j] - 4.)))) - (0.067 * (y4[i,j] - 2.52))) - (0.241 * (y5[i,j] + (y6[i,j] - 4.)))) - 0.) >= 0.0;


ineq79 'ID[4491491732]' 
  { (i,j) in dart_std3_mini } : 
  (((tau[j]) + ((0.0008 - (0.1631 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))) - (0.2127 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.)))))) - 0.) >= 0.0;


ineq80 'ID[1550635295]' 
  { (i,j) in dart_std3_mini } : 
  (((-(azim[i,j])) + (1.232 + (((0.261 * (y1[i,j] - 2.)) - (0.203 * (y2[i,j] + (y3[i,j] - 4.)))) + ((0.772 * (y4[i,j] - 2.)) - (0.191 * (y5[i,j] + (y6[i,j] - 4.))))))) - 0.) >= 0.0;


ineq81 'ID[9229542852]' 
  { (i,j) in dart_std3_mini } : 
  (((((azim[i,j]) - 1.23) - (0.2357 * (y1[i,j] - 2.))) + (((0.2493 * (y2[i,j] + (y3[i,j] - 4.))) - (0.682 * (y4[i,j] - 2.))) + (0.3035 * (y5[i,j] + (y6[i,j] - 4.))))) - 0.) >= 0.0;


ineq82 'ID[1085358243]' 
  { (i,j) in apex_sup_flat } : 
  (((((azim[i,j]) - 1.903) - (0.4 * (y1[i,j] - 2.))) + ((0.49688 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (y4[i,j] - (sqrt8)))) - 0.) >= 0.0;


ineq83 'ID[3566713650]' 
  { (i,j) in apex_sup_flat } : 
  (((-(azim[i,j])) + (1.911 + (((1.01 * (y1[i,j] - 2.)) - (0.284 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.)))))) + (1.07 * (y4[i,j] - (sqrt8)))))) - 0.) >= 0.0;


ineq84 'ID[7718591733]' 
  { (i,j) in apex_sup_flat } : 
  (((((azim2[i,j]) - 0.955) - (0.2356 * (y2[i,j] - 2.))) + ((0.32 * (y3[i,j] - 2.)) + (((0.792 * (y1[i,j] - 2.)) - (0.707 * (y5[i,j] - 2.))) + ((0.0844 * (y6[i,j] - 2.)) + (0.821 * (y4[i,j] - (sqrt8))))))) - 0.) >= 0.0;


ineq85 'ID[7863247282]' 
  { (i,j) in apex_sup_flat } : 
  ((((((tau[j]) - (0.053 * ((y5[i,j] + (y6[i,j] - 4.)) - ((2.75 / 2.) * (y4[i,j] - (sqrt8)))))) - 0.12) - (0.14132 * (y1[i,j] + ((y2[i,j] / 2.) + ((y3[i,j] / 2.) - 4.))))) - (0.328 * (y5[i,j] + (y6[i,j] - 4.)))) - 0.) >= 0.0;


ineq86 'ID[1642527039]' 
  { (i,j) in apex_sup_flat } : 
  ((((tau[j]) - 0.128) - (0.053 * ((y5[i,j] + (y6[i,j] - 4.)) - ((2.75 / 2.) * (y4[i,j] - (sqrt8)))))) - 0.) >= 0.0;


ineq87 'ID[4840774900]' 
  { (i,j) in apex_sup_flat } : 
  (((((tau[j]) - 0.1054) - (0.14132 * (y1[i,j] + ((y2[i,j] / 2.) + ((y3[i,j] / 2.) - 4.))))) - (0.36499 * (y5[i,j] + (y6[i,j] - 4.)))) - 0.) >= 0.0;


ineq88 'ID[5451229371]' 
  { (i,j) in apex_sup_flat } : 
  (((((tau[j]) - 0.11) - (0.14132 * (y1[i,j] + (((y2[i,j] + y3[i,j]) / 2.) - 4.)))) - (0.38 * (y5[i,j] + (y6[i,j] - 4.)))) - 0.) >= 0.0;


ineq89 'ID[6224332984]' 
  { (i,j) in dart_std3_big } : 
  ((((sol[j]) - 0.589) + ((0.39 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.)))) - (0.235 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.25)))))) - 0.) >= 0.0;


ineq90 'ID[7761782916]' 
  { (i,j) in dart_std3_big } : 
  (((((tau[j]) - 0.05) - (0.137 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))) - (0.17 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.25))))) - 0.) >= 0.0;


ineq91 'ID[9291937879]' 
  { (i,j) in dart_std3_small } : 
  (((((azim[i,j]) - 1.23) - (0.235 * (y1[i,j] - 2.))) + (((0.362 * (y2[i,j] + (y3[i,j] - 4.))) - (0.694 * (y4[i,j] - 2.))) + (0.26 * (y5[i,j] + (y6[i,j] - 4.))))) - 0.) >= 0.0;


ineq92 'ID[9225295803]' 
  { (i,j) in dart_std3_small } : 
  (((tau[j]) + ((0.0034 - (0.166 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))) - (0.22 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.)))))) - 0.) >= 0.0;


ineq93 'ID[7931207804]' 
  { (i,j) in apex_A } : 
  ((((tau[j]) - 0.27) + ((((((0.0295 * (y1[i,j] - 2.)) - (0.0778 * (y2[i,j] - 2.))) - (0.0778 * (y3[i,j] - 2.))) - (0.37 * (y4[i,j] - 2.))) - (0.27 * (y5[i,j] - 2.52))) - (0.27 * (y6[i,j] - 2.52)))) - 0.) >= 0.0;


ineq94 'ID[2563100177]' 
  { (i,j) in apex_A } : 
  (((((rhazim[i,j]) - 1.0685) - (0.4635 * (y1[i,j] - 2.))) + ((0.424 * (y2[i,j] - 2.)) + (((0.424 * (y3[i,j] - 2.)) - (0.594 * (y4[i,j] - 2.))) + ((0.124 * (y5[i,j] - 2.52)) + (0.124 * (y6[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq95 'ID[5760733457]' 
  { (i,j) in apex_A } : 
  (((((azim[i,j]) - 1.0705) - (0.1 * (y1[i,j] - 2.))) + ((0.424 * (y2[i,j] - 2.)) + (((0.424 * (y3[i,j] - 2.)) - (0.594 * (y4[i,j] - 2.))) + ((0.124 * (y5[i,j] - 2.52)) + (0.124 * (y6[i,j] - 2.52)))))) - 0.) >= 0.0;


ineq96 'ID[8082208587]' 
  { (i,j) in apex_A } : 
  ((tau[j]) - 0.2759) >= 0.0;


ineq97 'ID[9756015945]' 
  { (i,j) in apex_flat } : 
  ((((rhazim2[i,j]) - 1.08) + (((0.6362 * (y1[i,j] - 2.)) - (0.565 * (y2[i,j] - 2.))) + ((0.359 * (y3[i,j] - 2.)) + (((0.416 * (y4[i,j] - 2.52)) - (0.666 * (y5[i,j] - 2.))) + (0.061 * (y6[i,j] - 2.)))))) - 0.) >= 0.0;


ineq98 'ID[9251360200]' 
  { (i,j) in apex_flat } : 
  (((((rhazim[i,j]) - 1.629) - (0.866 * (y1[i,j] - 2.))) + (((0.3805 * (y2[i,j] + (y3[i,j] - 4.))) - (0.841 * (y4[i,j] - 2.52))) + (0.501 * (y5[i,j] + (y6[i,j] - 4.))))) - 0.) >= 0.0;


ineq99 'ID[5000076558]' 
  { (i,j) in apex_flat } : 
  ((((azim2[i,j]) - 1.083) + (((0.6365 * (y1[i,j] - 2.)) - (0.198 * (y2[i,j] - 2.))) + ((0.352 * (y3[i,j] - 2.)) + (((0.416 * (y4[i,j] - 2.52)) - (0.66 * (y5[i,j] - 2.))) + (0.071 * (y6[i,j] - 2.)))))) - 0.) >= 0.0;


ineq100 'ID[9922699028]' 
  { (i,j) in apex_flat } : 
  (((-(azim[i,j])) + ((1.6294 - (0.2213 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.)))))) + ((0.913 * (y4[i,j] - 2.52)) + (0.728 * (y1[i,j] - 2.))))) - 0.) >= 0.0;


ineq101 'ID[3318775219]' 
  { (i,j) in apex_flat } : 
  ((((azim[i,j]) - 1.629) + (((0.414 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.763 * (y4[i,j] - 2.52))) - (0.315 * (y1[i,j] - 2.)))) - 0.) >= 0.0;


ineq102 'ID[8248508703]' 
  { (i,j) in apex_flat } : 
  (((((((tau[j]) - 0.1) - (0.265 * (y5[i,j] + (y6[i,j] - 4.)))) - (0.06 * (y4[i,j] - 2.52))) - (0.16 * (y1[i,j] - 2.))) - (0.115 * (y2[i,j] + (y3[i,j] - 4.)))) - 0.) >= 0.0;


ineq103 'ID[6988401556]' 
  { (i,j) in apex_flat } : 
  ((tau[j]) - 0.103) >= 0.0;


ineq104 'ID[9995621667]' 
  { (i,j) in dart4_diag3 } : 
  ((((azim[i,j]) - 2.09) + ((0.578 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.54 * (y1[i,j] - 2.)))) - 0.) >= 0.0;


ineq105 'ID[9414951439]' 
  { (i,j) in dartY } : 
  ((((azim[i,j]) - 1.91) + ((0.458 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.342 * (y1[i,j] - 2.)))) - 0.) >= 0.0;


ineq106 'ID[3020140039]' 
  { (i,j) in dartX } : 
  ((((azim[i,j]) - 1.629) + ((0.402 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.315 * (y1[i,j] - 2.)))) - 0.) >= 0.0;


ineq107 'ID[5957966880]' 
  { (i,j) in dart_std3 } : 
  ((((rhazim[i,j]) - 1.2308) + (((0.3639 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.6 * (y1[i,j] - 2.))) - (0.685 * (y4[i,j] - 2.)))) - 0.) >= 0.0;


ineq108 'ID[3526497018]' 
  { (i,j) in dart_std3 } : 
  (((-(azim[i,j])) + ((1.231 - (0.152 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.)))))) + ((0.5 * (y1[i,j] - 2.)) + (0.773 * (y4[i,j] - 2.))))) - 0.) >= 0.0;


ineq109 'ID[4047599236]' 
  { (i,j) in dart_std3 } : 
  ((((azim[i,j]) - 1.2308) + (((0.3639 * (y2[i,j] + (y3[i,j] + (y5[i,j] + (y6[i,j] - 8.))))) - (0.235 * (y1[i,j] - 2.))) - (0.685 * (y4[i,j] - 2.)))) - 0.) >= 0.0;


ineq110 'ID[7726998381]' 
  { (i,j) in dart_std3 } : 
  (((-(sol[j])) + (0.5513 + ((0.3232 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.)))) - (0.151 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))))) - 0.) >= 0.0;


ineq111 'ID[7394240696]' 
  { (i,j) in dart_std3 } : 
  (((((sol[j]) - 0.55125) - (0.196 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.))))) + (0.38 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))) - 0.) >= 0.0;


ineq112 'ID[1395142356]' 
  { (i,j) in dart_std3 } : 
  (((tau[j]) + ((0.001 - (0.18 * (y1[i,j] + (y2[i,j] + (y3[i,j] - 6.))))) - (0.125 * (y4[i,j] + (y5[i,j] + (y6[i,j] - 6.)))))) - 0.) >= 0.0;


ineq113 'ID[4667071578]' 
  { (i,j) in dart_std3 } : 
  ((((tau[j]) - (0.507 * (azim[i,j]))) + 0.724) - 0.) >= 0.0;


ineq114 'ID[8519146937]' 
  { (i,j) in dart_std3 } : 
  ((((tau[j]) - (0.259 * (azim[i,j]))) + 0.32) - 0.) >= 0.0;


ineq115 'ID[3296257235]' 
  { (i,j) in dart_std3 } : 
  (((tau[j]) + ((0.626 * (azim[i,j])) - 0.77)) - 0.) >= 0.0;


ineq116 'ID[5490182221]' 
  { (i,j) in dart_std3 } : 
  (1.893 - (azim[i,j])) >= 0.0;


ineq117 'ID[5735387903]' 
  { (i,j) in dart_std3 } : 
  ((azim[i,j]) - 0.852) >= 0.0;


ineq118 'ID[9563139965D]' 
  { (i,j) in dart4_diag3_b } : 
  ((tau[j]) - 0.467) >= 0.0;


ineq119 'ID[3862621143 revised]' 
  { (i,j) in dart_std4 } : 
  ((((tau[j]) - (0.453 * (azim[i,j]))) + 0.777) - 0.) >= 0.0;


ineq120 'ID[4240815464 a]' 
  { (i,j) in dart_std4 } : 
  (((tau[j]) + ((0.7573 * (azim[i,j])) - 1.433)) - 0.) >= 0.0;

# test 7/2013. Remove this and 704...
#ineq121 'ID[6944699408 a]' 
#  { (i,j) in dart_std4 } : 
#  (((tau[j]) + ((0.972 * (azim[i,j])) - 1.707)) - 0.) >= 0.0;


#ineq122 'ID[7043724150 a]' 
#  { (i,j) in dart_std4 } : 
#  (((tau[j]) + ((4.72 * (azim[i,j])) - 6.248)) - 0.) >= 0.0;


# Symmetry section


ineq0 'ID[3137600529]' 
  { (i,j) in apex_flat_h } : 
  (((azim3[i,j]) + 0.0042) - (0.868174 + (((-0.701906) * ((-2.25) + y1[i,j])) + ((0.136514 * ((-2.) + y3[i,j])) + (((-0.209239) * ((-2.18) + y2[i,j])) + (((-0.493373) * ((-2.65) + y4[i,j])) + ((0.537385 * ((-2.) + y6[i,j])) + (0.0187672 * ((-2.2) + y5[i,j]))))))))) >= 0.0;


ineq1 'ID[6284721194]' 
  { (i,j) in apex_std3_hll } : 
  (((azim3[i,j]) + 0.0011) - (0.957661 + (((-0.250506) * ((-2.36) + y1[i,j])) + ((0.145114 * ((-2.1) + y3[i,j])) + (((-0.0549376) * ((-2.1) + y2[i,j])) + (((-0.0384445) * ((-2.45) + y4[i,j])) + ((0.5275 * ((-2.) + y6[i,j])) + (0.118819 * ((-2.45) + y5[i,j]))))))))) >= 0.0;


ineq2 'ID[9185711902]' 
  { (i,j) in apex_std3_hll } : 
  (((-(azim2[i,j])) + 0.0116) - ((-1.30119) + ((0.392915 * ((-2.36) + y1[i,j])) + ((0.142563 * ((-2.1) + y3[i,j])) + (((-0.258747) * ((-2.1) + y2[i,j])) + ((0.417088 * ((-2.45) + y4[i,j])) + (((-0.0606764) * ((-2.) + y6[i,j])) + ((-0.637966) * ((-2.45) + y5[i,j]))))))))) >= 0.0;


ineq3 'ID[6725783616]' 
  { (i,j) in apex_flat } : 
  (((azim2[i,j]) + 0.0046) - (0.88473 + (((-0.443946) * ((-2.36) + y1[i,j])) + (((-0.244711) * ((-2.1) + y3[i,j])) + ((0.205592 * ((-2.1) + y2[i,j])) + (((-0.739126) * ((-2.55) + y4[i,j])) + (((-0.127198) * ((-2.1) + y6[i,j])) + (0.61582 * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq4 'ID[1248932983]' 
  { (i,j) in apex_std3_lhh } : 
  (((-(azim3[i,j])) + 0.0059) - ((-1.33909) + ((0.0724529 * ((-2.) + y1[i,j])) + (((-0.486824) * ((-2.18) + y3[i,j])) + ((0.317329 * ((-2.18) + y2[i,j])) + (((-0.00479451) * ((-2.) + y4[i,j])) + (((-0.751179) * ((-2.25) + y6[i,j])) + (0.350857 * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq5 'ID[1836408787]' 
  { (i,j) in apex_std3_lhh } : 
  (((azim[i,j]) + 0.0012) - (1.01332 + ((0.148615 * ((-2.) + y1[i,j])) + (((-0.379006) * ((-2.18) + y3[i,j])) + (((-0.379441) * ((-2.18) + y2[i,j])) + ((0.583676 * ((-2.) + y4[i,j])) + (((-0.184708) * ((-2.25) + y6[i,j])) + ((-0.18471) * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq6 'ID[5943578801]' 
  { (i,j) in apex_sup_flat } : 
  (((azim3[i,j]) + 0.0047) - (0.936544 + (((-0.636113) * ((-2.1) + y1[i,j])) + ((0.140759 * ((-2.1) + y3[i,j])) + (((-0.0771734) * ((-2.3) + y2[i,j])) + (((-1.29068) * ((-2.82843) + y4[i,j])) + ((0.591328 * ((-2.1) + y6[i,j])) + ((-0.0521775) * ((-2.1) + y5[i,j]))))))))) >= 0.0;


ineq7 'ID[2763799127]' 
  { (i,j) in apex_sup_flat } : 
  (((-(azim2[i,j])) + 0.0076) - ((-0.956317) + ((0.419124 * ((-2.) + y1[i,j])) + (((-0.0753922) * ((-2.) + y3[i,j])) + (((-0.252307) * ((-2.) + y2[i,j])) + ((0.5 * ((-2.82843) + y4[i,j])) + (((-0.246082) * ((-2.) + y6[i,j])) + ((-0.788717) * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq8 'ID[4306175952]' 
  { (i,j) in dart_mll_n } : 
  (((azim3[i,j]) + 0.0035) - (1.05036 + (((-0.222178) * ((-2.18) + y1[i,j])) + ((0.132628 * ((-2.) + y3[i,j])) + (((-0.219284) * ((-2.) + y2[i,j])) + ((0.00563427 * ((-2.25) + y4[i,j])) + ((0.59096 * ((-2.) + y6[i,j])) + ((-0.0771574) * ((-2.52) + y5[i,j]))))))))) >= 0.0;


ineq9 'ID[2923748598]' 
  { (i,j) in dart_mll_n } : 
  (((-(azim[i,j])) + 0.0083) - ((-1.29912) + (((-0.284457) * ((-2.18) + y1[i,j])) + ((0.337354 * ((-2.) + y3[i,j])) + ((0.186287 * ((-2.) + y2[i,j])) + (((-0.645382) * ((-2.25) + y4[i,j])) + ((0.367671 * ((-2.52) + y6[i,j])) + (0.0536051 * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq10 'ID[6410081357]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((-(azim2[i,j])) + 0.0087) - ((-1.18616) + ((0.436647 * ((-2.18) + y1[i,j])) + ((0.032258 * ((-2.) + y3[i,j])) + (((-0.289629) * ((-2.) + y2[i,j])) + ((0.397053 * ((-2.52) + y4[i,j])) + (((-0.0210289) * ((-2.) + y6[i,j])) + ((-0.683341) * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq11 'ID[7316455966]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((azim3[i,j]) + 0.005) - (1.02005 + (((-0.256494) * ((-2.18) + y1[i,j])) + ((0.121497 * ((-2.) + y3[i,j])) + (((-0.256494) * ((-2.) + y2[i,j])) + (((-0.0116869) * ((-2.52) + y4[i,j])) + ((0.598233 * ((-2.) + y6[i,j])) + (0.0187672 * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq12 'ID[3425739813]' 
  { (i,j) in apex_flat } : 
  (((-(azim[i,j])) + 0.0011) - ((-1.67609) + (((-0.506322) * ((-2.18) + y1[i,j])) + ((0.212075 * ((-2.1) + y3[i,j])) + ((0.230669 * ((-2.1) + y2[i,j])) + (((-1.28579) * ((-2.52) + y4[i,j])) + ((0.249199 * ((-2.) + y6[i,j])) + (0.193545 * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq13 'ID[5756588587]' 
  { (i,j) in apex_std3_lll_wxx } : 
  (((azim3[i,j]) + 0.0025) - (1.16613 + (((-0.296776) * ((-2.) + y1[i,j])) + ((0.208935 * ((-2.) + y3[i,j])) + (((-0.196313) * ((-2.) + y2[i,j])) + (((-0.360575) * ((-2.25) + y4[i,j])) + ((0.652861 * ((-2.) + y6[i,j])) + ((-0.218063) * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq14 'ID[4222324842]' 
  { (i,j) in apex_std3_lll_xww } : 
  (((azim[i,j]) + 0.0071) - (1.09969 + ((0.146345 * ((-2.) + y1[i,j])) + (((-0.160538) * ((-2.) + y3[i,j])) + (((-0.151698) * ((-2.14) + y2[i,j])) + ((0.61314 * ((-2.) + y4[i,j])) + (((-0.236149) * ((-2.25) + y6[i,j])) + ((-0.242043) * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq15 'ID[9641946727]' 
  { (i,j) in apex_flat_l } : 
  (((azim3[i,j]) + 0.0071) - (0.98362 + (((-0.264094) * ((-2.18) + y1[i,j])) + ((0.149308 * ((-2.18) + y3[i,j])) + (((-0.312683) * ((-2.) + y2[i,j])) + (((-0.282792) * ((-2.65) + y4[i,j])) + ((0.581552 * ((-2.) + y6[i,j])) + (0.143669 * ((-2.3) + y5[i,j]))))))))) >= 0.0;


ineq16 'ID[2390583444]' 
  { (i,j) in dart_std3_mini } : 
  (((azim[i,j]) + 0.0012) - (1.08627 + ((0.159149 * ((-2.) + y1[i,j])) + (((-0.198496) * ((-2.1) + y3[i,j])) + (((-0.199306) * ((-2.1) + y2[i,j])) + ((0.590083 * ((-2.) + y4[i,j])) + (((-0.0888111) * ((-2.25) + y6[i,j])) + ((-0.0881846) * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq17 'ID[7291663656]' 
  { (i,j) in apex_flat } : 
  (((azim3[i,j]) + 0.0009) - (0.947391 + (((-0.637397) * ((-2.) + y1[i,j])) + ((0.120003 * ((-2.) + y3[i,j])) + (((-0.100814) * ((-2.3) + y2[i,j])) + (((-0.302956) * ((-2.65) + y4[i,j])) + ((0.547359 * ((-2.) + y6[i,j])) + ((-0.157745) * ((-2.2) + y5[i,j]))))))))) >= 0.0;


ineq18 'ID[6987934000]' 
  { (i,j) in dart_mll_w } : 
  (((azim3[i,j]) + 0.0042) - (0.952682 + (((-0.268837) * ((-2.36) + y1[i,j])) + ((0.130607 * ((-2.) + y3[i,j])) + (((-0.168729) * ((-2.) + y2[i,j])) + (((-0.0831764) * ((-2.52) + y4[i,j])) + ((0.580152 * ((-2.) + y6[i,j])) + (0.0656612 * ((-2.25) + y5[i,j]))))))))) >= 0.0;


ineq19 'ID[7819193535]' 
  { (i,j) in dart_std3_lw } : 
  (((azim3[i,j]) + 0.0011) - (1.16613 + (((-0.296776) * ((-2.) + y1[i,j])) + ((0.208935 * ((-2.) + y3[i,j])) + (((-0.243302) * ((-2.) + y2[i,j])) + (((-0.360575) * ((-2.25) + y4[i,j])) + ((0.636205 * ((-2.) + y6[i,j])) + ((-0.295156) * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq20 'ID[8384511215]' 
  { (i,j) in apex_flat } : 
  (((azim3[i,j]) + 0.0015) - (0.913186 + (((-0.390288) * ((-2.) + y1[i,j])) + ((0.115895 * ((-2.) + y3[i,j])) + ((0.164805 * ((-2.52) + y2[i,j])) + (((-0.271329) * ((-2.82843) + y4[i,j])) + ((0.584817 * ((-2.) + y6[i,j])) + ((-0.170218) * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq21 'ID[4750199435]' 
  { (i,j) in apex_flat } : 
  (((-(azim3[i,j])) + 0.0031) - ((-1.08346) + ((0.288794 * ((-2.) + y1[i,j])) + (((-0.292829) * ((-2.) + y3[i,j])) + ((0.036457 * ((-2.) + y2[i,j])) + ((0.348796 * ((-2.52) + y4[i,j])) + (((-0.762602) * ((-2.) + y6[i,j])) + ((-0.112679) * ((-2.) + y5[i,j]))))))))) >= 0.0;


ineq22 'ID[1894886027]' 
  { (i,j) in dart_Hll_w } : 
  ((1. * (azim3[i,j])) - (1.0494 + (((-0.401543) * (y1[i,j] - 2.36)) + ((0.207551 * (y3[i,j] - 2.)) + (((-0.0294227) * (y2[i,j] - 2.)) + (((-0.494954) * (y4[i,j] - 2.25)) + ((0.605453 * (y6[i,j] - 2.)) + ((-0.156385) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq23 'ID[5835568093]' 
  { (i,j) in dart_Hll_n } : 
  ((1. * (azim3[i,j])) - (1.0494 + (((-0.404131) * (y1[i,j] - 2.36)) + ((0.212119 * (y3[i,j] - 2.)) + (((-0.0402827) * (y2[i,j] - 2.)) + (((-0.299046) * (y4[i,j] - 2.25)) + ((0.643273 * (y6[i,j] - 2.)) + ((-0.266118) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq24 'ID[4002562507]' 
  { (i,j) in dart_mll_n } : 
  ((1. * (azim3[i,j])) - (1.0494 + (((-0.29013) * (y1[i,j] - 2.36)) + ((0.215328 * (y3[i,j] - 2.)) + (((-0.0715511) * (y2[i,j] - 2.)) + (((-0.267157) * (y4[i,j] - 2.25)) + ((0.650269 * (y6[i,j] - 2.)) + ((-0.295198) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq25 'ID[7409690040]' 
  { (i,j) in dart_mll_w } : 
  ((1. * (azim3[i,j])) - (1.0494 + (((-0.297823) * (y1[i,j] - 2.36)) + ((0.215328 * (y3[i,j] - 2.)) + (((-0.0792439) * (y2[i,j] - 2.)) + (((-0.422674) * (y4[i,j] - 2.25)) + ((0.647416 * (y6[i,j] - 2.)) + ((-0.207561) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq26 'ID[4041673283]' 
  { (i,j) in apex_std3_small_hll } : 
  (((-1.) * (azim3[i,j])) - ((-1.1864) + ((0.20758 * (y1[i,j] - 2.18)) + (((-0.236153) * (y3[i,j] - 2.)) + ((0.14172 * (y2[i,j] - 2.)) + ((0.263109 * (y4[i,j] - 2.)) + (((-0.737003) * (y6[i,j] - 2.)) + (0.12047 * (y5[i,j] - 2.))))))))) >= 0.0;


ineq27 'ID[1284543870]' 
  { (i,j) in apex_std3_small_hll } : 
  ((1. * (azim3[i,j])) - (1.185 + (((-0.372262) * (y1[i,j] - 2.18)) + ((0.214849 * (y3[i,j] - 2.)) + (((-0.163775) * (y2[i,j] - 2.)) + (((-0.293508) * (y4[i,j] - 2.)) + ((0.656172 * (y6[i,j] - 2.)) + ((-0.267157) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq28 'ID[7743522046]' 
  { (i,j) in apex_std3_hll } : 
  (((-1.) * (azim3[i,j])) - ((-1.1865) + ((0.20758 * (y1[i,j] - 2.18)) + (((-0.236153) * (y3[i,j] - 2.)) + ((0.14172 * (y2[i,j] - 2.)) + ((0.263834 * (y4[i,j] - 2.)) + (((-0.771203) * (y6[i,j] - 2.)) + (0.0457292 * (y5[i,j] - 2.))))))))) >= 0.0;


ineq29 'ID[5298513205]' 
  { (i,j) in apex_std3_hll } : 
  ((1. * (azim3[i,j])) - (1.185 + (((-0.302913) * (y1[i,j] - 2.18)) + ((0.214849 * (y3[i,j] - 2.)) + (((-0.163775) * (y2[i,j] - 2.)) + (((-0.443449) * (y4[i,j] - 2.)) + ((0.67364 * (y6[i,j] - 2.)) + ((-0.314532) * (y5[i,j] - 2.))))))))) >= 0.0;


ineq30 'ID[9756015945]' 
  { (i,j) in apex_flat } : 
  ((((rhazim3[i,j]) - 1.08) + (((0.6362 * (y1[i,j] - 2.)) - (0.565 * (y3[i,j] - 2.))) + ((0.359 * (y2[i,j] - 2.)) + (((0.416 * (y4[i,j] - 2.52)) - (0.666 * (y6[i,j] - 2.))) + (0.061 * (y5[i,j] - 2.)))))) - 0.) >= 0.0;


ineq31 'ID[5000076558]' 
  { (i,j) in apex_flat } : 
  ((((azim3[i,j]) - 1.083) + (((0.6365 * (y1[i,j] - 2.)) - (0.198 * (y3[i,j] - 2.))) + ((0.352 * (y2[i,j] - 2.)) + (((0.416 * (y4[i,j] - 2.52)) - (0.66 * (y6[i,j] - 2.))) + (0.071 * (y5[i,j] - 2.)))))) - 0.) >= 0.0;

