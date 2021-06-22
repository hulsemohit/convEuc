theory angleaddition
	imports Axioms Definitions Theorems
begin

theorem angleaddition:
	assumes: `axioms`
		"area_sum_eq A B C D E F P Q R"
		"ang_eq A B C a b c"
		"ang_eq D E F d e f"
		"area_sum_eq a b c d e f p q r"
	shows: "ang_eq P Q R p q r"
proof -
	obtain S where "ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R" sorry
	obtain s where "ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r" sorry
	have "ang_eq A B C P Q S" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "ang_eq D E F S Q R" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "bet P S R" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "ang_eq a b c p q s" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "ang_eq d e f s q r" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "\<not> col P Q S" using equalanglesNC[OF `axioms` `ang_eq A B C P Q S`] .
	have "\<not> col S Q R" using equalanglesNC[OF `axioms` `ang_eq D E F S Q R`] .
	have "Q \<noteq> P" using NCdistinct[OF `axioms` `\<not> col P Q S`] by blast
	have "Q \<noteq> S" using NCdistinct[OF `axioms` `\<not> col P Q S`] by blast
	have "Q \<noteq> R" using NCdistinct[OF `axioms` `\<not> col S Q R`] by blast
	have "\<not> col p q s" using equalanglesNC[OF `axioms` `ang_eq a b c p q s`] .
	have "\<not> col s q r" using equalanglesNC[OF `axioms` `ang_eq d e f s q r`] .
	have "q \<noteq> p" using NCdistinct[OF `axioms` `\<not> col p q s`] by blast
	have "q \<noteq> r" using NCdistinct[OF `axioms` `\<not> col s q r`] by blast
	have "q \<noteq> s" using NCdistinct[OF `axioms` `\<not> col p q s`] by blast
	obtain G where "ray_on q p G \<and> seg_eq q G Q P" using layoff[OF `axioms` `q \<noteq> p` `Q \<noteq> P`]  by  blast
	have "ray_on q p G" using `ray_on q p G \<and> seg_eq q G Q P` by blast
	obtain H where "ray_on q s H \<and> seg_eq q H Q S" using layoff[OF `axioms` `q \<noteq> s` `Q \<noteq> S`]  by  blast
	have "ray_on q s H" using `ray_on q s H \<and> seg_eq q H Q S` by blast
	obtain K where "ray_on q r K \<and> seg_eq q K Q R" using layoff[OF `axioms` `q \<noteq> r` `Q \<noteq> R`]  by  blast
	have "ray_on q r K" using `ray_on q r K \<and> seg_eq q K Q R` by blast
	have "seg_eq q K Q R" using `ray_on q r K \<and> seg_eq q K Q R` by blast
	have "ang_eq P Q S A B C" using equalanglessymmetric[OF `axioms` `ang_eq A B C P Q S`] .
	have "ang_eq P Q S a b c" using equalanglestransitive[OF `axioms` `ang_eq P Q S A B C` `ang_eq A B C a b c`] .
	have "ang_eq P Q S p q s" using equalanglestransitive[OF `axioms` `ang_eq P Q S a b c` `ang_eq a b c p q s`] .
	have "ang_eq P Q S G q H" using equalangleshelper[OF `axioms` `ang_eq P Q S p q s` `ray_on q p G` `ray_on q s H`] .
	have "ang_eq S Q R D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F S Q R`] .
	have "ang_eq S Q R d e f" using equalanglestransitive[OF `axioms` `ang_eq S Q R D E F` `ang_eq D E F d e f`] .
	have "ang_eq S Q R s q r" using equalanglestransitive[OF `axioms` `ang_eq S Q R d e f` `ang_eq d e f s q r`] .
	have "ang_eq S Q R H q K" using equalangleshelper[OF `axioms` `ang_eq S Q R s q r` `ray_on q s H` `ray_on q r K`] .
	have "\<not> col G q H" using equalanglesNC[OF `axioms` `ang_eq P Q S G q H`] .
	have "seg_eq q G Q P" using `ray_on q p G \<and> seg_eq q G Q P` by blast
	have "seg_eq q H Q S" using `ray_on q s H \<and> seg_eq q H Q S` by blast
	have "ang_eq G q H P Q S" using equalanglessymmetric[OF `axioms` `ang_eq P Q S G q H`] .
	have "seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P" using Prop04[OF `axioms` `seg_eq q G Q P` `seg_eq q H Q S` `ang_eq G q H P Q S`] .
	have "seg_eq G H P S" using `seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P` by blast
	have "ang_eq q H G Q S P" using `seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P` by blast
	have "ang_eq H q K S Q R" using equalanglessymmetric[OF `axioms` `ang_eq S Q R H q K`] .
	have "seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S" using Prop04[OF `axioms` `seg_eq q H Q S` `seg_eq q K Q R` `ang_eq H q K S Q R`] .
	have "seg_eq H K S R" using `seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S` by blast
	have "ang_eq q H K Q S R" using `seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S` by blast
	have "ang_eq G H q P S Q" using equalanglesflip[OF `axioms` `ang_eq q H G Q S P`] .
	have "Q = Q" using equalityreflexiveE[OF `axioms`] .
	have "S \<noteq> Q" using NCdistinct[OF `axioms` `\<not> col P Q S`] by blast
	have "ray_on S Q Q" using ray4 `axioms` `Q = Q` `S \<noteq> Q` by blast
	have "linear_pair P S Q Q R" sorry
	have "ang_suppl G H q q H K" sorry
	have "bet p s r" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "col q s H" using rayimpliescollinear[OF `axioms` `ray_on q s H`] .
	have "col q H s" using collinearorder[OF `axioms` `col q s H`] by blast
	have "\<not> col G q H" using `\<not> col G q H` .
	have "col q p G" using rayimpliescollinear[OF `axioms` `ray_on q p G`] .
	have "col G q p" using collinearorder[OF `axioms` `col q p G`] by blast
	have "q = q" using equalityreflexiveE[OF `axioms`] .
	have "col G q q" using col_b `axioms` `q = q` by blast
	have "q \<noteq> p" using ray2[OF `axioms` `ray_on q p G`] .
	have "p \<noteq> q" using inequalitysymmetric[OF `axioms` `q \<noteq> p`] .
	have "\<not> col p q H" using NChelper[OF `axioms` `\<not> col G q H` `col G q p` `col G q q` `p \<noteq> q`] .
	have "\<not> col q H p" using NCorder[OF `axioms` `\<not> col p q H`] by blast
	have "oppo_side p q H r" sorry
	have "oppo_side r q H p" using oppositesidesymmetric[OF `axioms` `oppo_side p q H r`] .
	have "col q H q" using col_b `axioms` `q = q` by blast
	have "ray_on q K r" using ray5[OF `axioms` `ray_on q r K`] .
	have "oppo_side K q H p" using n9_5[OF `axioms` `oppo_side r q H p` `ray_on q K r` `col q H q`] .
	have "oppo_side p q H K" using oppositesidesymmetric[OF `axioms` `oppo_side K q H p`] .
	have "ray_on q G p" using ray5[OF `axioms` `ray_on q p G`] .
	have "oppo_side G q H K" using n9_5[OF `axioms` `oppo_side p q H K` `ray_on q G p` `col q H q`] .
	have "oppo_side K q H G" using oppositesidesymmetric[OF `axioms` `oppo_side G q H K`] .
	have "q \<noteq> H" using raystrict[OF `axioms` `ray_on q s H`] .
	have "H \<noteq> q" using inequalitysymmetric[OF `axioms` `q \<noteq> H`] .
	have "ray_on H q q" using ray4 `axioms` `q = q` `H \<noteq> q` by blast
	have "bet G H K" using Prop14[OF `axioms` `ang_suppl G H q q H K` `ray_on H q q` `oppo_side K q H G`] by blast
	have "seg_eq G K P R" using sumofparts[OF `axioms` `seg_eq G H P S` `seg_eq H K S R` `bet G H K` `bet P S R`] .
	have "seg_eq q G Q P" using `seg_eq q G Q P` .
	have "seg_eq q K Q R" using `seg_eq q K Q R` .
	have "P = P" using equalityreflexiveE[OF `axioms`] .
	have "R = R" using equalityreflexiveE[OF `axioms`] .
	have "ray_on Q P P" using ray4 `axioms` `P = P` `Q \<noteq> P` by blast
	have "ray_on Q R R" using ray4 `axioms` `R = R` `Q \<noteq> R` by blast
	have "\<not> col P S Q" using NCorder[OF `axioms` `\<not> col P Q S`] by blast
	have "col P S R" using col_b `axioms` `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "P = P" using equalityreflexiveE[OF `axioms`] .
	have "col P S P" using col_b `axioms` `P = P` by blast
	have "P \<noteq> R" using betweennotequal[OF `axioms` `bet P S R`] by blast
	have "\<not> col P R Q" using NChelper[OF `axioms` `\<not> col P S Q` `col P S P` `col P S R` `P \<noteq> R`] .
	have "\<not> col P Q R" using NCorder[OF `axioms` `\<not> col P R Q`] by blast
	have "seg_eq Q P q G" using congruencesymmetric[OF `axioms` `seg_eq q G Q P`] .
	have "seg_eq Q R q K" using congruencesymmetric[OF `axioms` `seg_eq q K Q R`] .
	have "seg_eq P R G K" using congruencesymmetric[OF `axioms` `seg_eq G K P R`] .
	have "ang_eq P Q R p q r" sorry
	thus ?thesis by blast
qed

end