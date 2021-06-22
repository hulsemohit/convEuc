theory Prop42
	imports Axioms Definitions Theorems
begin

theorem Prop42:
	assumes: `axioms`
		"triangle A B C"
		"\<not> col J D K"
		"midpoint B E C"
	shows: "\<exists> F G. parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A"
proof -
	have "bet B E C \<and> seg_eq B E E C" sorry
	have "bet B E C" using `bet B E C \<and> seg_eq B E E C` by blast
	have "seg_eq B E E C" using `bet B E C \<and> seg_eq B E E C` by blast
	have "seg_eq E B E C" using congruenceflip[OF `axioms` `seg_eq B E E C`] by blast
	have "\<not> col A B C" sorry
	have "col B E C" using col_b `axioms` `bet B E C \<and> seg_eq B E E C` by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col B C E" using collinearorder[OF `axioms` `col B E C`] by blast
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col B C C" using col_b `axioms` `C = C` by blast
	have "E \<noteq> C" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "\<not> col E C A" using NChelper[OF `axioms` `\<not> col B C A` `col B C E` `col B C C` `E \<noteq> C`] .
	obtain c f where "ray_on E C c \<and> ang_eq f E c J D K \<and> same_side f A E C" using Prop23C[OF `axioms` `E \<noteq> C` `\<not> col J D K` `\<not> col E C A`]  by  blast
	have "same_side f A E C" using `ray_on E C c \<and> ang_eq f E c J D K \<and> same_side f A E C` by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	obtain M P Q where "bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E" using Prop31[OF `axioms` `bet B E C` `\<not> col B C A`]  by  blast
	have "bet P A Q" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "ang_eq P A E A E C" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "bet P M C" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "bet A M E" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "seg_eq P M M C" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "seg_eq A M M E" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "seg_eq B M M Q" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "ang_eq A E C P A E" using equalanglessymmetric[OF `axioms` `ang_eq P A E A E C`] .
	have "\<not> col P A E" using equalanglesNC[OF `axioms` `ang_eq A E C P A E`] .
	have "\<not> col E A P" using NCorder[OF `axioms` `\<not> col P A E`] by blast
	have "same_side A f E C" using samesidesymmetric[OF `axioms` `same_side f A E C`] by blast
	have "\<not> col B C A" using NCorder[OF `axioms` `\<not> col A B C`] by blast
	have "col B C E" using collinearorder[OF `axioms` `col B E C`] by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "col B C B" using col_b `axioms` `B = B` by blast
	have "B \<noteq> E" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "\<not> col B E A" using NChelper[OF `axioms` `\<not> col B C A` `col B C B` `col B C E` `B \<noteq> E`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "col B C C" using col_b `axioms` `C = C` by blast
	have "E \<noteq> C" using betweennotequal[OF `axioms` `bet B E C`] by blast
	have "C \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> C`] .
	have "\<not> col C E A" using NChelper[OF `axioms` `\<not> col B C A` `col B C C` `col B C E` `C \<noteq> E`] .
	have "E \<noteq> A" using NCdistinct[OF `axioms` `\<not> col B E A`] by blast
	have "meets E f P Q"
	proof (rule ccontr)
		assume "\<not> (meets E f P Q)"
		have "\<not> (ang_lt C E f C E A)"
		proof (rule ccontr)
			assume "ang_lt C E f C E A"
			have "ray_on E C C" using ray4 `axioms` `C = C` `E \<noteq> C` by blast
			have "ray_on E A A" using ray4 `axioms` `A = A` `E \<noteq> A` by blast
			obtain m where "bet A m C \<and> ray_on E f m" using crossbar2[OF `axioms` `ang_lt C E f C E A` `same_side f A E C` `ray_on E C C` `ray_on E A A`]  by  blast
			have "bet A m C" using `bet A m C \<and> ray_on E f m` by blast
			have "ray_on E f m" using `bet A m C \<and> ray_on E f m` by blast
			have "bet C m A" using betweennesssymmetryE[OF `axioms` `bet A m C`] .
			have "bet C M P" using betweennesssymmetryE[OF `axioms` `bet P M C`] .
			have "bet E M A" using betweennesssymmetryE[OF `axioms` `bet A M E`] .
			have "seg_eq M E A M" using congruencesymmetric[OF `axioms` `seg_eq A M M E`] .
			have "seg_eq E M A M" using congruenceflip[OF `axioms` `seg_eq M E A M`] by blast
			have "seg_eq M C P M" using congruencesymmetric[OF `axioms` `seg_eq P M M C`] .
			have "seg_eq M C M P" using congruenceflip[OF `axioms` `seg_eq M C P M`] by blast
			obtain F where "bet E m F \<and> bet P A F" using Euclid5E[OF `axioms` `bet C M P` `bet E M A` `bet C m A` `seg_eq E M A M` `seg_eq M C M P`]  by  blast
			have "bet E m F" using `bet E m F \<and> bet P A F` by blast
			have "bet P A F" using `bet E m F \<and> bet P A F` by blast
			have "col E m F" using col_b `axioms` `bet E m F \<and> bet P A F` by blast
			have "col m E F" using collinearorder[OF `axioms` `col E m F`] by blast
			have "col E f m" using rayimpliescollinear[OF `axioms` `ray_on E f m`] .
			have "col m E f" using collinearorder[OF `axioms` `col E f m`] by blast
			have "E \<noteq> m" using betweennotequal[OF `axioms` `bet E m F`] by blast
			have "m \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> m`] .
			have "col E f F" using collinear4[OF `axioms` `col m E f` `col m E F` `m \<noteq> E`] .
			have "col P A F" using col_b `axioms` `bet E m F \<and> bet P A F` by blast
			have "col P A Q" using col_b `axioms` `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
			have "P \<noteq> A" using betweennotequal[OF `axioms` `bet P A F`] by blast
			have "A \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> A`] .
			have "col A P F" using collinearorder[OF `axioms` `col P A F`] by blast
			have "col A P Q" using collinearorder[OF `axioms` `col P A Q`] by blast
			have "col P F Q" using collinear4[OF `axioms` `col A P F` `col A P Q` `A \<noteq> P`] .
			have "col P Q F" using collinearorder[OF `axioms` `col P F Q`] by blast
			have "E \<noteq> f" using ray2[OF `axioms` `ray_on E f m`] .
			have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P A Q`] by blast
			have "meets E f P Q" sorry
			show "False" using `meets E f P Q` `\<not> (meets E f P Q)` by blast
		qed
		hence "\<not> (ang_lt C E f C E A)" by blast
		have "col E C B" using collinearorder[OF `axioms` `col B C E`] by blast
		have "B \<noteq> E" using betweennotequal[OF `axioms` `bet B E C`] by blast
		have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
		have "same_side A f E B" using samesidecollinear[OF `axioms` `same_side A f E C` `col E C B` `E \<noteq> B`] .
		have "same_side f A E B" using samesidesymmetric[OF `axioms` `same_side A f E B`] by blast
		have "bet C E B" using betweennesssymmetryE[OF `axioms` `bet B E C`] .
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "f = f" using equalityreflexiveE[OF `axioms`] .
		have "\<not> col E B f" sorry
		have "E \<noteq> f" using NCdistinct[OF `axioms` `\<not> col E B f`] by blast
		have "col B E C" using col_b `axioms` `bet B E C \<and> seg_eq B E E C` by blast
		have "col E B C" using collinearorder[OF `axioms` `col B C E`] by blast
		have "E = E" using equalityreflexiveE[OF `axioms`] .
		have "col E B E" using col_b `axioms` `E = E` by blast
		have "\<not> col E C f" using NChelper[OF `axioms` `\<not> col E B f` `col E B E` `col E B C` `E \<noteq> C`] .
		have "\<not> col C E f" using NCorder[OF `axioms` `\<not> col E C f`] by blast
		have "\<not> (ang_lt C E A C E f)"
		proof (rule ccontr)
			assume "ang_lt C E A C E f"
			have "ray_on E A A" using ray4 `axioms` `A = A` `E \<noteq> A` by blast
			have "ray_on E f f" using ray4 `axioms` `f = f` `E \<noteq> f` by blast
			have "linear_pair C E A A B" sorry
			have "linear_pair C E f f B" sorry
			have "ang_lt f E B A E B" using supplementinequality[OF `axioms` `linear_pair C E f f B` `linear_pair C E A A B` `ang_lt C E A C E f`] .
			have "\<not> col B E f" using NCorder[OF `axioms` `\<not> col E B f`] by blast
			have "ang_eq B E f f E B" using ABCequalsCBA[OF `axioms` `\<not> col B E f`] .
			have "ang_lt B E f A E B" using angleorderrespectscongruence2[OF `axioms` `ang_lt f E B A E B` `ang_eq B E f f E B`] .
			have "ang_eq B E A A E B" using ABCequalsCBA[OF `axioms` `\<not> col B E A`] .
			have "ang_lt B E f B E A" using angleorderrespectscongruence[OF `axioms` `ang_lt B E f A E B` `ang_eq B E A A E B`] .
			have "ray_on E B B" using ray4 `axioms` `B = B` `E \<noteq> B` by blast
			have "ray_on E A A" using ray4 `axioms` `A = A` `E \<noteq> A` by blast
			obtain m where "bet A m B \<and> ray_on E f m" using crossbar2[OF `axioms` `ang_lt B E f B E A` `same_side f A E B` `ray_on E B B` `ray_on E A A`]  by  blast
			have "bet A m B" using `bet A m B \<and> ray_on E f m` by blast
			have "ray_on E f m" using `bet A m B \<and> ray_on E f m` by blast
			have "bet B m A" using betweennesssymmetryE[OF `axioms` `bet A m B`] .
			have "bet B M Q" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
			have "bet E M A" using betweennesssymmetryE[OF `axioms` `bet A M E`] .
			have "seg_eq M E A M" using congruencesymmetric[OF `axioms` `seg_eq A M M E`] .
			have "seg_eq E M A M" using congruenceflip[OF `axioms` `seg_eq M E A M`] by blast
			have "seg_eq M B M Q" using congruenceflip[OF `axioms` `seg_eq B M M Q`] by blast
			have "\<not> col E A P" using `\<not> col E A P` .
			have "\<not> col P A E" using NCorder[OF `axioms` `\<not> col E A P`] by blast
			have "col P A Q" using col_b `axioms` `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
			have "A = A" using equalityreflexiveE[OF `axioms`] .
			have "col P A A" using col_b `axioms` `A = A` by blast
			have "A \<noteq> Q" using betweennotequal[OF `axioms` `bet P A Q`] by blast
			have "Q \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> Q`] .
			have "\<not> col Q A E" using NChelper[OF `axioms` `\<not> col P A E` `col P A Q` `col P A A` `Q \<noteq> A`] .
			have "\<not> col E A Q" using NCorder[OF `axioms` `\<not> col Q A E`] by blast
			obtain F where "bet E m F \<and> bet Q A F" using Euclid5E[OF `axioms` `bet B M Q` `bet E M A` `bet B m A` `seg_eq E M A M` `seg_eq M B M Q`]  by  blast
			have "bet E m F" using `bet E m F \<and> bet Q A F` by blast
			have "bet Q A F" using `bet E m F \<and> bet Q A F` by blast
			have "col E m F" using col_b `axioms` `bet E m F \<and> bet Q A F` by blast
			have "col m E F" using collinearorder[OF `axioms` `col E m F`] by blast
			have "col E f m" using rayimpliescollinear[OF `axioms` `ray_on E f m`] .
			have "col m E f" using collinearorder[OF `axioms` `col E f m`] by blast
			have "E \<noteq> m" using betweennotequal[OF `axioms` `bet E m F`] by blast
			have "m \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> m`] .
			have "col E f F" using collinear4[OF `axioms` `col m E f` `col m E F` `m \<noteq> E`] .
			have "col Q A F" using col_b `axioms` `bet E m F \<and> bet Q A F` by blast
			have "bet Q A P" using betweennesssymmetryE[OF `axioms` `bet P A Q`] .
			have "col Q A P" using col_b `axioms` `bet Q A P` by blast
			have "Q \<noteq> A" using betweennotequal[OF `axioms` `bet Q A F`] by blast
			have "A \<noteq> Q" using inequalitysymmetric[OF `axioms` `Q \<noteq> A`] .
			have "col A Q F" using collinearorder[OF `axioms` `col Q A F`] by blast
			have "col A Q P" using collinearorder[OF `axioms` `col P A Q`] by blast
			have "col Q F P" using collinear4[OF `axioms` `col A Q F` `col A Q P` `A \<noteq> Q`] .
			have "col P Q F" using collinearorder[OF `axioms` `col Q F P`] by blast
			have "E \<noteq> f" using ray2[OF `axioms` `ray_on E f f`] .
			have "Q \<noteq> P" using betweennotequal[OF `axioms` `bet Q A P`] by blast
			have "P \<noteq> Q" using inequalitysymmetric[OF `axioms` `Q \<noteq> P`] .
			have "meets E f P Q" sorry
			show "False" using `meets E f P Q` `\<not> (meets E f P Q)` by blast
		qed
		hence "\<not> (ang_lt C E A C E f)" by blast
		have "ang_eq C E A C E f"
		proof (rule ccontr)
			assume "\<not> (ang_eq C E A C E f)"
			have "\<not> col C E A" using `\<not> col C E A` .
			have "\<not> col C E f" using `\<not> col C E f` .
			have "ang_lt C E A C E f" using angletrichotomy2[OF `axioms` `\<not> col C E A` `\<not> col C E f` `\<not> (ang_eq C E A C E f)` `\<not> (ang_lt C E f C E A)`] .
			show "False" using `ang_lt C E A C E f` `\<not> (ang_lt C E A C E f)` by blast
		qed
		hence "ang_eq C E A C E f" by blast
		obtain a d p q where "ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A" sorry
		have "ray_on E A a" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "ray_on E f q" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "ray_on E C p" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "ray_on E C d" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "seg_eq E d E p" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "seg_eq E a E q" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "seg_eq d a p q" using `ray_on E C d \<and> ray_on E A a \<and> ray_on E C p \<and> ray_on E f q \<and> seg_eq E d E p \<and> seg_eq E a E q \<and> seg_eq d a p q \<and> \<not> col C E A` by blast
		have "col P Q A" using col_b `axioms` `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
		have "d = p" using layoffunique[OF `axioms` `ray_on E C d` `ray_on E C p` `seg_eq E d E p`] .
		have "seg_eq d a d q" sorry
		have "seg_eq a d q d" using congruenceflip[OF `axioms` `seg_eq d a d q`] by blast
		have "seg_eq a E q E" using congruenceflip[OF `axioms` `seg_eq E a E q`] by blast
		have "E \<noteq> d" using raystrict[OF `axioms` `ray_on E C d`] .
		have "same_side A f E C" using `same_side A f E C` .
		have "col E C d" using rayimpliescollinear[OF `axioms` `ray_on E C d`] .
		have "same_side A f E d" using samesidecollinear[OF `axioms` `same_side A f E C` `col E C d` `E \<noteq> d`] .
		have "col E d E" using col_b `axioms` `E = E` by blast
		have "col E E d" using collinearorder[OF `axioms` `col E d E`] by blast
		have "same_side A q E d" using sameside2[OF `axioms` `same_side A f E d` `col E E d` `ray_on E f q`] .
		have "same_side q A E d" using samesidesymmetric[OF `axioms` `same_side A q E d`] by blast
		have "same_side q a E d" using sameside2[OF `axioms` `same_side q A E d` `col E E d` `ray_on E A a`] .
		have "same_side a q E d" using samesidesymmetric[OF `axioms` `same_side q a E d`] by blast
		have "a = q" using Prop07[OF `axioms` `E \<noteq> d` `seg_eq a E q E` `seg_eq a d q d` `same_side a q E d`] .
		have "col E A a" using rayimpliescollinear[OF `axioms` `ray_on E A a`] .
		have "col E f q" using rayimpliescollinear[OF `axioms` `ray_on E f q`] .
		have "col E A q" sorry
		have "col q E A" using collinearorder[OF `axioms` `col E A q`] by blast
		have "col q E f" using collinearorder[OF `axioms` `col E f q`] by blast
		have "E \<noteq> q" using raystrict[OF `axioms` `ray_on E f q`] .
		have "q \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> q`] .
		have "col E A f" using collinear4[OF `axioms` `col q E A` `col q E f` `q \<noteq> E`] .
		have "col E f A" using collinearorder[OF `axioms` `col E A f`] by blast
		have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P A Q`] by blast
		have "meets E f P Q" sorry
		show "False" using `meets E f P Q` `\<not> (meets E f P Q)` by blast
	qed
	hence "meets E f P Q" by blast
	obtain F where "E \<noteq> f \<and> P \<noteq> Q \<and> col E f F \<and> col P Q F" sorry
	have "P \<noteq> Q" using `E \<noteq> f \<and> P \<noteq> Q \<and> col E f F \<and> col P Q F` by blast
	have "parallel P Q B C" using `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "col B C E" using `col B C E` .
	have "C \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> C`] .
	have "parallel P Q E C" using collinearparallel[OF `axioms` `parallel P Q B C` `col B C E` `E \<noteq> C`] .
	have "parallel E C P Q" using parallelsymmetric[OF `axioms` `parallel P Q E C`] .
	have "col P Q F" using `E \<noteq> f \<and> P \<noteq> Q \<and> col E f F \<and> col P Q F` by blast
	obtain G where "parallelogram F G C E \<and> col P Q G" using triangletoparallelogram[OF `axioms` `parallel E C P Q` `col P Q F`]  by  blast
	have "parallelogram F G C E" using `parallelogram F G C E \<and> col P Q G` by blast
	have "parallelogram G F E C" using PGflip[OF `axioms` `parallelogram F G C E`] .
	have "parallelogram F E C G" using PGrotate[OF `axioms` `parallelogram G F E C`] .
	have "col P Q F" using `col P Q F` .
	have "col P Q G" using `parallelogram F G C E \<and> col P Q G` by blast
	have "col P A Q" using col_b `axioms` `bet P A Q \<and> ang_eq Q A E A E B \<and> ang_eq Q A E B E A \<and> ang_eq E A Q B E A \<and> ang_eq P A E A E C \<and> ang_eq P A E C E A \<and> ang_eq E A P C E A \<and> parallel P Q B C \<and> seg_eq P A E C \<and> seg_eq A Q B E \<and> seg_eq A M M E \<and> seg_eq P M M C \<and> seg_eq B M M Q \<and> bet P M C \<and> bet B M Q \<and> bet A M E` by blast
	have "col P Q A" using collinearorder[OF `axioms` `col P A Q`] by blast
	have "parallel F E C G" sorry
	have "\<not> col F E G" using parallelNC[OF `axioms` `parallel F E C G`] by blast
	have "F \<noteq> G" using NCdistinct[OF `axioms` `\<not> col F E G`] by blast
	have "col F G A" using collinear5[OF `axioms` `P \<noteq> Q` `col P Q F` `col P Q G` `col P Q A`] .
	have "tri_eq_area F E C A E C" using Prop41[OF `axioms` `parallelogram F E C G` `col F G A`] .
	have "parallel P Q C B" using parallelflip[OF `axioms` `parallel P Q B C`] by blast
	have "col C B E" using collinearorder[OF `axioms` `col B C E`] by blast
	have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
	have "parallel P Q E B" using collinearparallel[OF `axioms` `parallel P Q C B` `col C B E` `E \<noteq> B`] .
	have "parallel P Q B E" using parallelflip[OF `axioms` `parallel P Q E B`] by blast
	have "col P Q A" using `col P Q A` .
	have "seg_eq B E E C" using congruenceflip[OF `axioms` `seg_eq E B E C`] by blast
	have "col B E C" using `col B E C` .
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col B E E" using col_b `axioms` `E = E` by blast
	have "tri_eq_area A B E A E C" using Prop38[OF `axioms` `parallel P Q B E` `col P Q A` `col P Q A` `seg_eq B E E C` `col B E E` `col B E C`] .
	have "tri_eq_area A E C A B E" using ETsymmetricE[OF `axioms` `tri_eq_area A B E A E C`] .
	have "tri_eq_area A E C A E B" using ETpermutationE[OF `axioms` `tri_eq_area A E C A B E`] by blast
	have "tri_eq_area A E B A E C" using ETsymmetricE[OF `axioms` `tri_eq_area A E C A E B`] .
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "col A E E" using col_b `axioms` `E = E` by blast
	have "\<not> col A E B" using NCorder[OF `axioms` `\<not> col B E A`] by blast
	have "oppo_side B A E C" sorry
	have "parallelogram F E C G" using `parallelogram F E C G` .
	have "parallelogram E F G C" using PGflip[OF `axioms` `parallelogram F E C G`] .
	have "tri_cong F E C C G F" using Prop34[OF `axioms` `parallelogram E F G C`] by blast
	have "tri_eq_area F E C C G F" using congruentequalE[OF `axioms` `tri_cong F E C C G F`] .
	have "tri_eq_area F E C F C G" using ETpermutationE[OF `axioms` `tri_eq_area F E C C G F`] by blast
	have "tri_eq_area F C G F E C" using ETsymmetricE[OF `axioms` `tri_eq_area F E C F C G`] .
	have "tri_eq_area F C G F C E" using ETpermutationE[OF `axioms` `tri_eq_area F C G F E C`] by blast
	have "tri_eq_area F C E F C G" using ETsymmetricE[OF `axioms` `tri_eq_area F C G F C E`] .
	obtain m where "bet E m G \<and> bet F m C" using diagonalsmeet[OF `axioms` `parallelogram E F G C`]  by  blast
	have "bet E m G" using `bet E m G \<and> bet F m C` by blast
	have "bet F m C" using `bet E m G \<and> bet F m C` by blast
	have "col F m C" using col_b `axioms` `bet E m G \<and> bet F m C` by blast
	have "col F C m" using collinearorder[OF `axioms` `col F m C`] by blast
	have "parallel F E C G" sorry
	have "\<not> col F E C" using parallelNC[OF `axioms` `parallel F E C G`] by blast
	have "\<not> col F C E" using NCorder[OF `axioms` `\<not> col F E C`] by blast
	have "oppo_side E F C G" sorry
	have "tri_eq_area F C E F C G" using `tri_eq_area F C E F C G` .
	have "tri_eq_area A E B A E C" using `tri_eq_area A E B A E C` .
	have "tri_eq_area F E C A E C" using `tri_eq_area F E C A E C` .
	have "tri_eq_area A E C F E C" using ETsymmetricE[OF `axioms` `tri_eq_area F E C A E C`] .
	have "tri_eq_area A E B F E C" using ETtransitiveE[OF `axioms` `tri_eq_area A E B A E C` `tri_eq_area A E C F E C`] .
	have "tri_eq_area A E B F C E" using ETpermutationE[OF `axioms` `tri_eq_area A E B F E C`] by blast
	have "tri_eq_area A E C F E C" using ETsymmetricE[OF `axioms` `tri_eq_area F E C A E C`] .
	have "tri_eq_area F C G F C E" using ETsymmetricE[OF `axioms` `tri_eq_area F C E F C G`] .
	have "tri_eq_area F C G F E C" using ETpermutationE[OF `axioms` `tri_eq_area F C G F C E`] by blast
	have "tri_eq_area F E C F C G" using ETsymmetricE[OF `axioms` `tri_eq_area F C G F E C`] .
	have "tri_eq_area A E C F C G" using ETtransitiveE[OF `axioms` `tri_eq_area A E C F E C` `tri_eq_area F E C F C G`] .
	have "qua_eq_area A B E C F E C G" sorry
	have "ray_on E C c" using `ray_on E C c \<and> ang_eq f E c J D K \<and> same_side f A E C` by blast
	have "\<not> col F E C" using parallelNC[OF `axioms` `parallel F E C G`] by blast
	have "\<not> col C E F" using NCorder[OF `axioms` `\<not> col F C E`] by blast
	have "ang_eq C E F C E F" using equalanglesreflexive[OF `axioms` `\<not> col C E F`] .
	have "col E f F" using `E \<noteq> f \<and> P \<noteq> Q \<and> col E f F \<and> col P Q F` by blast
	have "same_side f A E C" using `same_side f A E C` .
	have "E = f \<or> E = F \<or> f = F \<or> bet f E F \<or> bet E f F \<or> bet E F f" using col_f[OF `axioms` `col E f F`] .
	have "F \<noteq> E" using NCdistinct[OF `axioms` `\<not> col C E F`] by blast
	have "E \<noteq> F" using inequalitysymmetric[OF `axioms` `F \<noteq> E`] .
	consider "E = f"|"E = F"|"f = F"|"bet f E F"|"bet E f F"|"bet E F f" using `E = f \<or> E = F \<or> f = F \<or> bet f E F \<or> bet E f F \<or> bet E F f`  by blast
	hence ray_on E F f
	proof (cases)
		case 1
		have "ray_on E F f"
		proof (rule ccontr)
			assume "\<not> (ray_on E F f)"
			have "E \<noteq> f" using `E \<noteq> f \<and> P \<noteq> Q \<and> col E f F \<and> col P Q F` by blast
			show "False" using `E \<noteq> f` `E = f` by blast
		qed
		hence "ray_on E F f" by blast
	next
		case 2
		have "ray_on E F f"
		proof (rule ccontr)
			assume "\<not> (ray_on E F f)"
			have "E \<noteq> F" using `E \<noteq> F` .
			show "False" using `E \<noteq> F` `E = F` by blast
		qed
		hence "ray_on E F f" by blast
	next
		case 3
		have "F = F" using equalityreflexiveE[OF `axioms`] .
		have "E \<noteq> F" using `E \<noteq> F` .
		have "ray_on E F F" using ray4 `axioms` `F = F` `E \<noteq> F` by blast
		have "ray_on E F f" sorry
	next
		case 4
		have "ray_on E F f"
		proof (rule ccontr)
			assume "\<not> (ray_on E F f)"
			have "E = E" using equalityreflexiveE[OF `axioms`] .
			have "col E C E" using col_b `axioms` `E = E` by blast
			have "bet F E f" using betweennesssymmetryE[OF `axioms` `bet f E F`] .
			have "\<not> col E C F" using NCorder[OF `axioms` `\<not> col C E F`] by blast
			have "oppo_side F E C f" sorry
			have "oppo_side f E C F" using oppositesidesymmetric[OF `axioms` `oppo_side F E C f`] .
			have "same_side A f E C" using samesidesymmetric[OF `axioms` `same_side f A E C`] by blast
			have "oppo_side A E C F" using planeseparation[OF `axioms` `same_side A f E C` `oppo_side f E C F`] .
			obtain j where "bet A j F \<and> col E C j \<and> \<not> col E C A" sorry
			have "bet A j F" using `bet A j F \<and> col E C j \<and> \<not> col E C A` by blast
			have "col E C j" using `bet A j F \<and> col E C j \<and> \<not> col E C A` by blast
			have "col A j F" using col_b `axioms` `bet A j F \<and> col E C j \<and> \<not> col E C A` by blast
			have "col P Q A" using `col P Q A` .
			have "col P Q F" using `col P Q F` .
			have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P A Q`] by blast
			have "Q \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> Q`] .
			have "col Q A F" using collinear4[OF `axioms` `col P Q A` `col P Q F` `P \<noteq> Q`] .
			have "col A F Q" using collinearorder[OF `axioms` `col Q A F`] by blast
			have "col Q P A" using collinearorder[OF `axioms` `col P A Q`] by blast
			have "col Q P F" using collinearorder[OF `axioms` `col P Q F`] by blast
			have "col P A F" using collinear4[OF `axioms` `col Q P A` `col Q P F` `Q \<noteq> P`] .
			have "col A F P" using collinearorder[OF `axioms` `col P A F`] by blast
			have "col A F j" using collinearorder[OF `axioms` `col A j F`] by blast
			have "P \<noteq> Q" using betweennotequal[OF `axioms` `bet P A Q`] by blast
			have "A \<noteq> F" using betweennotequal[OF `axioms` `bet A j F`] by blast
			have "col P Q j" using collinear5[OF `axioms` `A \<noteq> F` `col A F P` `col A F Q` `col A F j`] .
			have "meets P Q E C" sorry
			have "parallel P Q E C" using `parallel P Q E C` .
			have "\<not> (meets P Q E C)" sorry
			show "False" using `\<not> (meets P Q E C)` `meets P Q E C` by blast
		qed
		hence "ray_on E F f" by blast
	next
		case 5
		have "ray_on E F f" using ray4 `axioms` `bet E f F` `E \<noteq> F` by blast
	next
		case 6
		have "ray_on E F f" using ray4 `axioms` `bet E F f` `E \<noteq> F` by blast
	next
	have "ang_eq C E F c E f" using equalangleshelper[OF `axioms` `ang_eq C E F C E F` `ray_on E C c` `ray_on E F f`] .
	have "ang_eq F E C f E c" using equalanglesflip[OF `axioms` `ang_eq C E F c E f`] .
	have "ang_eq f E c J D K" using `ray_on E C c \<and> ang_eq f E c J D K \<and> same_side f A E C` by blast
	have "ang_eq F E C J D K" using equalanglestransitive[OF `axioms` `ang_eq F E C f E c` `ang_eq f E c J D K`] .
	have "ang_eq C E F F E C" using ABCequalsCBA[OF `axioms` `\<not> col C E F`] .
	have "ang_eq C E F J D K" using equalanglestransitive[OF `axioms` `ang_eq C E F F E C` `ang_eq F E C J D K`] .
	have "parallelogram F E C G \<and> qua_eq_area A B E C F E C G \<and> ang_eq C E F J D K \<and> col F G A" using `parallelogram F E C G` `qua_eq_area A B E C F E C G` `ang_eq C E F J D K` `col F G A` by blast
	thus ?thesis by blast
qed

end