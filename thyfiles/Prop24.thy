theory Prop24
	imports Axioms Definitions Theorems
begin

theorem Prop24:
	assumes: `axioms`
		"triangle A B C"
		"triangle D E F"
		"seg_eq A B D E"
		"seg_eq A C D F"
		"ang_lt E D F B A C"
	shows: "seg_lt E F B C"
proof -
	have "\<not> col A B C" sorry
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using col_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using col_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using col_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain P Q T where "bet P T Q \<and> ray_on A B P \<and> ray_on A C Q \<and> ang_eq E D F B A T" sorry
	have "ray_on A B P" using `bet P T Q \<and> ray_on A B P \<and> ray_on A C Q \<and> ang_eq E D F B A T` by blast
	have "ray_on A C Q" using `bet P T Q \<and> ray_on A B P \<and> ray_on A C Q \<and> ang_eq E D F B A T` by blast
	have "ang_eq E D F B A T" using `bet P T Q \<and> ray_on A B P \<and> ray_on A C Q \<and> ang_eq E D F B A T` by blast
	have "\<not> col B A T" using equalanglesNC[OF `axioms` `ang_eq E D F B A T`] .
	have "\<not> (A = T)"
	proof (rule ccontr)
		assume "A = T"
		have "col B A T" using col_b `axioms` `A = T` by blast
		show "False" using `col B A T` `\<not> col B A T` by blast
	qed
	hence "A \<noteq> T" by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using col_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	obtain H where "ray_on A T H \<and> seg_eq A H A C" using layoff[OF `axioms` `A \<noteq> T` `A \<noteq> C`]  by  blast
	have "ray_on A T H" using `ray_on A T H \<and> seg_eq A H A C` by blast
	have "seg_eq A H A C" using `ray_on A T H \<and> seg_eq A H A C` by blast
	have "seg_eq A C D F" using `seg_eq A C D F` .
	have "seg_eq A H D F" using congruencetransitive[OF `axioms` `seg_eq A H A C` `seg_eq A C D F`] .
	have "\<not> (col H A B)"
	proof (rule ccontr)
		assume "col H A B"
		have "col A T H" using rayimpliescollinear[OF `axioms` `ray_on A T H`] .
		have "col H A T" using collinearorder[OF `axioms` `col A T H`] by blast
		have "A \<noteq> H" using raystrict[OF `axioms` `ray_on A T H`] .
		have "H \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> H`] .
		have "col A B T" using collinear4[OF `axioms` `col H A B` `col H A T` `H \<noteq> A`] .
		have "col B A T" using collinearorder[OF `axioms` `col A B T`] by blast
		show "False" using `col B A T` `\<not> col B A T` by blast
	qed
	hence "\<not> col H A B" by blast
	have "\<not> (H = B)"
	proof (rule ccontr)
		assume "H = B"
		have "col H A B" using col_b `axioms` `H = B` by blast
		show "False" using `col H A B` `\<not> col H A B` by blast
	qed
	hence "H \<noteq> B" by blast
	have "seg_eq A B D E" using `seg_eq A B D E` .
	have "ang_eq E D F B A T" using `ang_eq E D F B A T` .
	have "ray_on A T H" using `ray_on A T H` .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "ray_on A B B" using ray4 `axioms` `B = B` `A \<noteq> B` by blast
	have "ang_eq E D F B A H" using equalangleshelper[OF `axioms` `ang_eq E D F B A T` `ray_on A B B` `ray_on A T H`] .
	have "ang_eq B A H E D F" using equalanglessymmetric[OF `axioms` `ang_eq E D F B A H`] .
	have "ang_eq H A B F D E" using equalanglesflip[OF `axioms` `ang_eq B A H E D F`] .
	have "seg_eq H B F E \<and> ang_eq A H B D F E \<and> ang_eq A B H D E F" using Prop04[OF `axioms` `seg_eq A H D F` `seg_eq A B D E` `ang_eq H A B F D E`] .
	have "ray_on A Q C" using ray5[OF `axioms` `ray_on A C Q`] .
	have "ray_on A P B" using ray5[OF `axioms` `ray_on A B P`] .
	have "col A Q C" using rayimpliescollinear[OF `axioms` `ray_on A Q C`] .
	have "col A P B" using rayimpliescollinear[OF `axioms` `ray_on A P B`] .
	have "\<not> (col Q A P)"
	proof (rule ccontr)
		assume "col Q A P"
		have "col A P Q" using collinearorder[OF `axioms` `col Q A P`] by blast
		have "col Q A C" using collinearorder[OF `axioms` `col A Q C`] by blast
		have "col Q A P" using collinearorder[OF `axioms` `col A P Q`] by blast
		have "A \<noteq> Q" using ray2[OF `axioms` `ray_on A Q C`] .
		have "Q \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> Q`] .
		have "col A C P" using collinear4[OF `axioms` `col Q A C` `col Q A P` `Q \<noteq> A`] .
		have "col P A B" using collinearorder[OF `axioms` `col A P B`] by blast
		have "col P A C" using collinearorder[OF `axioms` `col A C P`] by blast
		have "A \<noteq> P" using raystrict[OF `axioms` `ray_on A B P`] .
		have "P \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> P`] .
		have "col A B C" using collinear4[OF `axioms` `col P A B` `col P A C` `P \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col Q A P" by blast
	have "triangle Q A P" sorry
	have "bet P T Q" using `bet P T Q \<and> ray_on A B P \<and> ray_on A C Q \<and> ang_eq E D F B A T` by blast
	have "bet Q T P" using betweennesssymmetryE[OF `axioms` `bet P T Q`] .
	obtain J where "ray_on A T J \<and> bet C J B" using crossbar[OF `axioms` `triangle Q A P` `bet Q T P` `ray_on A Q C` `ray_on A P B`]  by  blast
	have "ray_on A T J" using `ray_on A T J \<and> bet C J B` by blast
	have "bet C J B" using `ray_on A T J \<and> bet C J B` by blast
	have "ray_on A T H" using `ray_on A T H` .
	have "ray_on A J H" using ray3[OF `axioms` `ray_on A T J` `ray_on A T H`] .
	have "seg_eq A C A H" using congruencesymmetric[OF `axioms` `seg_eq A H A C`] .
	have "\<not> (col A C H)"
	proof (rule ccontr)
		assume "col A C H"
		have "col H A C" using collinearorder[OF `axioms` `col A C H`] by blast
		have "A \<noteq> H" using raystrict[OF `axioms` `ray_on A J H`] .
		have "H \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> H`] .
		have "col A J H" using rayimpliescollinear[OF `axioms` `ray_on A J H`] .
		have "col H A J" using collinearorder[OF `axioms` `col A J H`] by blast
		have "col A C J" using collinear4[OF `axioms` `col H A C` `col H A J` `H \<noteq> A`] .
		have "col C J B" using col_b `axioms` `ray_on A T J \<and> bet C J B` by blast
		have "col C J A" using collinearorder[OF `axioms` `col A C J`] by blast
		have "C \<noteq> J" using betweennotequal[OF `axioms` `bet C J B`] by blast
		have "col J B A" using collinear4[OF `axioms` `col C J B` `col C J A` `C \<noteq> J`] .
		have "col A T J" using rayimpliescollinear[OF `axioms` `ray_on A T J`] .
		have "col J A T" using collinearorder[OF `axioms` `col A T J`] by blast
		have "col J A B" using collinearorder[OF `axioms` `col J B A`] by blast
		have "A \<noteq> J" using raystrict[OF `axioms` `ray_on A T J`] .
		have "J \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> J`] .
		have "col A T B" using collinear4[OF `axioms` `col J A T` `col J A B` `J \<noteq> A`] .
		have "col B A T" using collinearorder[OF `axioms` `col A T B`] by blast
		show "False" using `col B A T` `\<not> col B A T` by blast
	qed
	hence "\<not> col A C H" by blast
	have "triangle A C H" sorry
	have "tri_isos A C H" sorry
	have "ang_eq A C H A H C" using Prop05[OF `axioms` `tri_isos A C H`] .
	have "bet A H J \<or> J = H \<or> bet A J H" using ray1[OF `axioms` `ray_on A J H`] .
	consider "bet A H J"|"J = H"|"bet A J H" using `bet A H J \<or> J = H \<or> bet A J H`  by blast
	hence seg_lt H B C B
	proof (cases)
		case 1
		have "\<not> (col C J H)"
		proof (rule ccontr)
			assume "col C J H"
			have "col A H J" using col_b `axioms` `bet A H J` by blast
			have "col J H A" using collinearorder[OF `axioms` `col A H J`] by blast
			have "col J H C" using collinearorder[OF `axioms` `col C J H`] by blast
			have "H \<noteq> J" using betweennotequal[OF `axioms` `bet A H J`] by blast
			have "J \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> J`] .
			have "col H A C" using collinear4[OF `axioms` `col J H A` `col J H C` `J \<noteq> H`] .
			have "col A C H" using collinearorder[OF `axioms` `col H A C`] by blast
			show "False" using `col A C H` `\<not> col A C H` by blast
		qed
		hence "\<not> col C J H" by blast
		have "triangle C J H" sorry
		have "bet J H A" using betweennesssymmetryE[OF `axioms` `bet A H J`] .
		have "ang_lt J C H C H A" using Prop16[OF `axioms` `triangle C J H` `bet J H A`] by blast
		have "\<not> (col H C J)"
		proof (rule ccontr)
			assume "col H C J"
			have "col C J H" using collinearorder[OF `axioms` `col H C J`] by blast
			show "False" using `col C J H` `\<not> col C J H` by blast
		qed
		hence "\<not> col H C J" by blast
		have "ang_eq H C J J C H" using ABCequalsCBA[OF `axioms` `\<not> col H C J`] .
		have "ang_lt H C J C H A" using angleorderrespectscongruence2[OF `axioms` `ang_lt J C H C H A` `ang_eq H C J J C H`] .
		have "\<not> (col A H C)"
		proof (rule ccontr)
			assume "col A H C"
			have "col A C H" using collinearorder[OF `axioms` `col A H C`] by blast
			show "False" using `col A C H` `\<not> col A C H` by blast
		qed
		hence "\<not> col A H C" by blast
		have "ang_eq A H C C H A" using ABCequalsCBA[OF `axioms` `\<not> col A H C`] .
		have "ang_lt H C J A H C" using angleorderrespectscongruence[OF `axioms` `ang_lt H C J C H A` `ang_eq A H C C H A`] .
		have "ray_on H B B" using ray4 `axioms` `B = B` `H \<noteq> B` by blast
		have "bet C J B" using `bet C J B` .
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "\<not> (col C H J)"
		proof (rule ccontr)
			assume "col C H J"
			have "col C J H" using collinearorder[OF `axioms` `col C H J`] by blast
			show "False" using `col C J H` `\<not> col C J H` by blast
		qed
		hence "\<not> col C H J" by blast
		have "\<not> (C = H)"
		proof (rule ccontr)
			assume "C = H"
			have "col C H J" using col_b `axioms` `C = H` by blast
			show "False" using `col C H J` `\<not> col C H J` by blast
		qed
		hence "C \<noteq> H" by blast
		have "H \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> H`] .
		have "ray_on H C C" using ray4 `axioms` `C = C` `H \<noteq> C` by blast
		have "ang_eq C H J C H J" using equalanglesreflexive[OF `axioms` `\<not> col C H J`] .
		have "C \<noteq> J" using angledistinct[OF `axioms` `ang_eq C H J C H J`] by blast
		have "C \<noteq> H" using angledistinct[OF `axioms` `ang_eq A C H A H C`] by blast
		have "ang_lt C H J C H B" sorry
		have "\<not> (col C A H)"
		proof (rule ccontr)
			assume "col C A H"
			have "col A C H" using collinearorder[OF `axioms` `col C A H`] by blast
			have "\<not> col A C H" using `\<not> col A C H` .
			show "False" using `\<not> col A C H` `col A C H` by blast
		qed
		hence "\<not> col C A H" by blast
		have "triangle C A H" sorry
		have "ang_lt A C H C H J" using Prop16[OF `axioms` `triangle C A H` `bet A H J`] by blast
		have "ang_lt H C J A H C" using `ang_lt H C J A H C` .
		have "ang_eq A C H A H C" using `ang_eq A C H A H C` .
		have "ang_lt H C J A C H" using angleorderrespectscongruence[OF `axioms` `ang_lt H C J A H C` `ang_eq A C H A H C`] .
		have "ang_lt A C H C H J" using `ang_lt A C H C H J` .
		have "ang_lt H C J C H J" using angleordertransitive[OF `axioms` `ang_lt H C J A C H` `ang_lt A C H C H J`] .
		have "ang_lt C H J C H B" using `ang_lt C H J C H B` .
		have "ang_lt H C J C H B" using angleordertransitive[OF `axioms` `ang_lt H C J C H J` `ang_lt C H J C H B`] .
		have "H = H" using equalityreflexiveE[OF `axioms`] .
		have "ray_on C H H" using ray4 `axioms` `H = H` `C \<noteq> H` by blast
		have "ray_on C J B" using ray4 `axioms` `ray_on A T J \<and> bet C J B` `C \<noteq> J` by blast
		have "ang_eq H C J H C J" using equalanglesreflexive[OF `axioms` `\<not> col H C J`] .
		have "ang_eq H C J H C B" using equalangleshelper[OF `axioms` `ang_eq H C J H C J` `ray_on C H H` `ray_on C J B`] .
		have "ang_eq H C B H C J" using equalanglessymmetric[OF `axioms` `ang_eq H C J H C B`] .
		have "ang_lt H C B C H B" using angleorderrespectscongruence2[OF `axioms` `ang_lt H C J C H B` `ang_eq H C B H C J`] .
		have "\<not> (col B H C)"
		proof (rule ccontr)
			assume "col B H C"
			have "col C J B" using col_b `axioms` `ray_on A T J \<and> bet C J B` by blast
			have "col B C H" using collinearorder[OF `axioms` `col B H C`] by blast
			have "col B C J" using collinearorder[OF `axioms` `col C J B`] by blast
			have "C \<noteq> B" using betweennotequal[OF `axioms` `bet C J B`] by blast
			have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
			have "col C H J" using collinear4[OF `axioms` `col B C H` `col B C J` `B \<noteq> C`] .
			show "False" using `col C H J` `\<not> col C H J` by blast
		qed
		hence "\<not> col B H C" by blast
		have "triangle B H C" sorry
		have "ang_eq B H C C H B" using ABCequalsCBA[OF `axioms` `\<not> col B H C`] .
		have "ang_lt H C B B H C" using angleorderrespectscongruence[OF `axioms` `ang_lt H C B C H B` `ang_eq B H C C H B`] .
		have "seg_lt B H B C" using Prop19[OF `axioms` `triangle B H C` `ang_lt H C B B H C`] .
		have "seg_eq B H H B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B B C" using lessthancongruence2[OF `axioms` `seg_lt B H B C` `seg_eq B H H B`] .
		have "seg_eq B C C B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B C B" using lessthancongruence[OF `axioms` `seg_lt H B B C` `seg_eq B C C B`] .
	next
		case 2
		have "bet C H B" sorry
		have "bet B H C" using betweennesssymmetryE[OF `axioms` `bet C H B`] .
		have "seg_eq B H H B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B B C" sorry
		have "seg_eq B C C B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B C B" using lessthancongruence[OF `axioms` `seg_lt H B B C` `seg_eq B C C B`] .
	next
		case 3
		have "bet H J A" using betweennesssymmetryE[OF `axioms` `bet A J H`] .
		have "\<not> (col C J H)"
		proof (rule ccontr)
			assume "col C J H"
			have "col A H J" using col_b `axioms` `bet A J H` by blast
			have "col J H A" using collinearorder[OF `axioms` `col A H J`] by blast
			have "col J H C" using collinearorder[OF `axioms` `col C J H`] by blast
			have "H \<noteq> J" using betweennotequal[OF `axioms` `bet H J A`] by blast
			have "J \<noteq> H" using inequalitysymmetric[OF `axioms` `H \<noteq> J`] .
			have "col H A C" using collinear4[OF `axioms` `col J H A` `col J H C` `J \<noteq> H`] .
			have "col A C H" using collinearorder[OF `axioms` `col H A C`] by blast
			show "False" using `col A C H` `\<not> col A C H` by blast
		qed
		hence "\<not> col C J H" by blast
		have "\<not> (col H C B)"
		proof (rule ccontr)
			assume "col H C B"
			have "col C J B" using col_b `axioms` `ray_on A T J \<and> bet C J B` by blast
			have "col B C J" using collinearorder[OF `axioms` `col C J B`] by blast
			have "col B C H" using collinearorder[OF `axioms` `col H C B`] by blast
			have "C \<noteq> B" using betweennotequal[OF `axioms` `bet C J B`] by blast
			have "B \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> B`] .
			have "col C H J" using collinear4[OF `axioms` `col B C H` `col B C J` `B \<noteq> C`] .
			have "col C J H" using collinearorder[OF `axioms` `col C H J`] by blast
			have "\<not> col C J H" using `\<not> col C J H` .
			show "False" using `\<not> col C J H` `col C J H` by blast
		qed
		hence "\<not> col H C B" by blast
		have "H = H" using equalityreflexiveE[OF `axioms`] .
		have "A = A" using equalityreflexiveE[OF `axioms`] .
		have "\<not> (C = H)"
		proof (rule ccontr)
			assume "C = H"
			have "col C H B" using col_b `axioms` `C = H` by blast
			have "col H C B" using collinearorder[OF `axioms` `col C H B`] by blast
			show "False" using `col H C B` `\<not> col H C B` by blast
		qed
		hence "C \<noteq> H" by blast
		have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
		have "ang_eq H C B H C B" using equalanglesreflexive[OF `axioms` `\<not> col H C B`] .
		have "ray_on C B J" using ray4 `axioms` `ray_on A T J \<and> bet C J B` `C \<noteq> B` by blast
		have "ray_on C H H" using ray4 `axioms` `H = H` `C \<noteq> H` by blast
		have "ang_eq H C B H C J" using equalangleshelper[OF `axioms` `ang_eq H C B H C B` `ray_on C H H` `ray_on C B J`] .
		have "bet H J A" using betweennesssymmetryE[OF `axioms` `bet A J H`] .
		have "ang_lt H C B H C A" sorry
		have "\<not> (col B C H)"
		proof (rule ccontr)
			assume "col B C H"
			have "col H C B" using collinearorder[OF `axioms` `col B C H`] by blast
			show "False" using `col H C B` `\<not> col H C B` by blast
		qed
		hence "\<not> col B C H" by blast
		have "ang_eq B C H H C B" using ABCequalsCBA[OF `axioms` `\<not> col B C H`] .
		have "ang_lt B C H H C A" using angleorderrespectscongruence2[OF `axioms` `ang_lt H C B H C A` `ang_eq B C H H C B`] .
		have "\<not> col A C H" using `\<not> col A C H` .
		have "ang_eq A C H H C A" using ABCequalsCBA[OF `axioms` `\<not> col A C H`] .
		have "ang_lt B C H A C H" using angleorderrespectscongruence[OF `axioms` `ang_lt B C H H C A` `ang_eq A C H H C A`] .
		have "ang_eq A C H A H C" using `ang_eq A C H A H C` .
		have "ang_eq A H C A C H" using equalanglessymmetric[OF `axioms` `ang_eq A C H A H C`] .
		have "ang_lt B C H A H C" using angleorderrespectscongruence[OF `axioms` `ang_lt B C H A C H` `ang_eq A H C A C H`] .
		have "\<not> (col A H C)"
		proof (rule ccontr)
			assume "col A H C"
			have "col A C H" using collinearorder[OF `axioms` `col A H C`] by blast
			show "False" using `col A C H` `\<not> col A C H` by blast
		qed
		hence "\<not> col A H C" by blast
		have "ang_eq A H C C H A" using ABCequalsCBA[OF `axioms` `\<not> col A H C`] .
		have "C = C" using equalityreflexiveE[OF `axioms`] .
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "H \<noteq> B" using angledistinct `axioms` `seg_eq H B F E \<and> ang_eq A H B D F E \<and> ang_eq A B H D E F` by blast
		have "H \<noteq> C" using angledistinct[OF `axioms` `ang_eq A C H A H C`] by blast
		have "H \<noteq> A" using angledistinct[OF `axioms` `ang_eq A C H H C A`] by blast
		have "ray_on H C C" using ray4 `axioms` `C = C` `H \<noteq> C` by blast
		have "ray_on H B B" using ray4 `axioms` `B = B` `H \<noteq> B` by blast
		have "ray_on H A J" using ray4 `axioms` `bet H J A` `H \<noteq> A` by blast
		have "ang_eq A H C C H J" using equalangleshelper[OF `axioms` `ang_eq A H C C H A` `ray_on H C C` `ray_on H A J`] .
		have "bet C J B" using `bet C J B` .
		have "ang_lt A H C C H B" sorry
		have "\<not> (col B H C)"
		proof (rule ccontr)
			assume "col B H C"
			have "col H C B" using collinearorder[OF `axioms` `col B H C`] by blast
			show "False" using `col H C B` `\<not> col H C B` by blast
		qed
		hence "\<not> col B H C" by blast
		have "ang_eq B H C C H B" using ABCequalsCBA[OF `axioms` `\<not> col B H C`] .
		have "ang_lt A H C B H C" using angleorderrespectscongruence[OF `axioms` `ang_lt A H C C H B` `ang_eq B H C C H B`] .
		have "ang_lt B C H B H C" using angleordertransitive[OF `axioms` `ang_lt B C H A H C` `ang_lt A H C B H C`] .
		have "\<not> (col H C B)"
		proof (rule ccontr)
			assume "col H C B"
			have "col B H C" using collinearorder[OF `axioms` `col H C B`] by blast
			show "False" using `col B H C` `\<not> col B H C` by blast
		qed
		hence "\<not> col H C B" by blast
		have "ang_eq H C B B C H" using ABCequalsCBA[OF `axioms` `\<not> col H C B`] .
		have "ang_lt H C B B H C" using angleorderrespectscongruence2[OF `axioms` `ang_lt B C H B H C` `ang_eq H C B B C H`] .
		have "triangle B H C" sorry
		have "seg_lt B H B C" using Prop19[OF `axioms` `triangle B H C` `ang_lt H C B B H C`] .
		have "seg_eq B H H B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B B C" using lessthancongruence2[OF `axioms` `seg_lt B H B C` `seg_eq B H H B`] .
		have "seg_eq B C C B" using equalityreverseE[OF `axioms`] .
		have "seg_lt H B C B" using lessthancongruence[OF `axioms` `seg_lt H B B C` `seg_eq B C C B`] .
	next
	have "seg_eq H B F E" using `seg_eq H B F E \<and> ang_eq A H B D F E \<and> ang_eq A B H D E F` by blast
	have "seg_eq F E E F" using equalityreverseE[OF `axioms`] .
	have "seg_eq H B E F" using congruencetransitive[OF `axioms` `seg_eq H B F E` `seg_eq F E E F`] .
	have "seg_lt E F C B" using lessthancongruence2[OF `axioms` `seg_lt H B C B` `seg_eq H B E F`] .
	have "seg_eq C B B C" using equalityreverseE[OF `axioms`] .
	have "seg_lt E F B C" using lessthancongruence[OF `axioms` `seg_lt E F C B` `seg_eq C B B C`] .
	thus ?thesis by blast
qed

end