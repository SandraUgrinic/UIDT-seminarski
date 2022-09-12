theory seminarski
  imports Main Complex_Main

begin

(*
https://www.imo-official.org/problems/IMO2008SL.pdf

Zadatak A2:
(a) Prove the inequality
    x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 \<ge> 1
for real numbers x, y, z \<noteq> 1 satisfying the condition x * y * z = 1.

(b) Show that there are infinitely many triples of rational numbers 
x, y, z for which this inequality turns into equality.
*)

(* Izraz koji se nalazi sa leve strane nejednakosti *)
fun izraz :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real" where
  "izraz x y z = (x^2)/(x-1)^2 + (y^2)/(y-1)^2 + (z^2)/(z-1)^2"


(* Uvodim promenljive a, b, c*)
fun a :: "real \<Rightarrow> real" where
"a x = x / (x - 1)"

fun b :: "real \<Rightarrow> real" where
"b y = y / (y - 1)"

fun c :: "real \<Rightarrow> real" where
"c z = z / (z - 1)"


(* 
  Zapisujem levu stranu nejednakosti preko promenljivih
  a, b, c koje sam uvela i dokazujem jednakost ta dva.  
*)
lemma dokaz_jednakosti:
  assumes "\<forall> x y z :: real. x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1"
      shows "izraz x y z = (a x)^2 + (b y)^2 + (c z)^2"
  using assms
  by blast


lemma zadatak_a:
  assumes "\<forall> x y z :: real. x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1"
  shows "(a x)^2 + (b y)^2 + (c z)^2 \<ge> 1"
  using assms
  (*by blast *)
proof-
  have "(a x - 1) * (b y - 1) * (c z - 1) = a x * b x * c y"
    using assms
    by blast
  then have "(a x * b y - a x - b y + 1) * (c z - 1) = a x * b y * c z"
    using assms
    by blast
  then have "a x * b y * c z - a x * b y - a x * c z + a x - b y * c z + b y + c z - 1 = a x * b y * c z"
    using assms
    by blast
  then have "a x + b y + c z - 1 = a x * b y + b y * c z + c z * a x"
    using assms
    by blast
  then have "a x + b y + c z - 1 = ((a x + b y + c z)^2 - ((a x)^2 + (b y)^2 + (c z)^2)) / 2"
    using assms
    by blast
  then have "2 * (a x + b y + c z - 1) = (a x + b y + c z)^2 - ((a x)^2 + (b y)^2 + (c z)^2)"
    using assms
    by blast
  then have "(a x)^2 + (b y)^2 + (c z)^2 - 2 = (a x + b y + c z)^2 - 2*(a x + b y + c z)"
    using assms
    by blast
  then have "(a x)^2 + (b y)^2 + (c z)^2 - 1 = (a x + b y + c z - 1)^2"
    using assms
    by blast
  then have "((a x)^2 + (b y)^2 + (c z)^2) = 1 + (a x + b y + c z - 1) ^ 2"
    using assms
    by blast
  then have "((a x)^2 + (b y)^2 + (c z)^2) \<ge> 1"
    by auto
  then show ?thesis
  using assms
  by auto
qed


(*
  (b) Show that there are infinitely many triples of rational numbers 
  x, y, z for which this inequality turns into equality.
*)
lemma zadatak_b:
  assumes "\<forall> x y z :: real. x \<noteq> 1 \<and> y \<noteq> 1 \<and> z \<noteq> 1 \<and> x * y * z = 1"
  shows "(a x)^2 + (b y)^2 + (c z)^2 = 1  "
  using assms
  by auto


end