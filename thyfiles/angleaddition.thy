theory angleaddition
	imports n9_5 Geometry NCdistinct NChelper NCorder Prop04 Prop14 betweennotequal collinearorder congruencesymmetric equalanglesNC equalanglesflip equalangleshelper equalanglessymmetric equalanglestransitive inequalitysymmetric layoff oppositesidesymmetric ray2 ray4 ray5 rayimpliescollinear raystrict sumofparts
begin

theorem(in euclidean_geometry) angleaddition:
	assumes 
		"area_sum_eq A B C D E F P Q R"
		"ang_eq A B C a b c"
		"ang_eq D E F d e f"
		"area_sum_eq a b c d e f p q r"
	shows "ang_eq P Q R p q r"
proof -
	obtain S where "ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R" using anglesum_f[OF `area_sum_eq A B C D E F P Q R`]  by  blast
	obtain s where "ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r" using anglesum_f[OF `area_sum_eq a b c d e f p q r`]  by  blast
	have "ang_eq A B C P Q S" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "ang_eq D E F S Q R" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "bet P S R" using `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "ang_eq a b c p q s" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "ang_eq d e f s q r" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "\<not> col P Q S" using equalanglesNC[OF `ang_eq A B C P Q S`] .
	have "\<not> col S Q R" using equalanglesNC[OF `ang_eq D E F S Q R`] .
	have "Q \<noteq> P" using NCdistinct[OF `\<not> col P Q S`] by blast
	have "Q \<noteq> S" using NCdistinct[OF `\<not> col P Q S`] by blast
	have "Q \<noteq> R" using NCdistinct[OF `\<not> col S Q R`] by blast
	have "\<not> col p q s" using equalanglesNC[OF `ang_eq a b c p q s`] .
	have "\<not> col s q r" using equalanglesNC[OF `ang_eq d e f s q r`] .
	have "q \<noteq> p" using NCdistinct[OF `\<not> col p q s`] by blast
	have "q \<noteq> r" using NCdistinct[OF `\<not> col s q r`] by blast
	have "q \<noteq> s" using NCdistinct[OF `\<not> col p q s`] by blast
	obtain G where "ray_on q p G \<and> seg_eq q G Q P" using layoff[OF `q \<noteq> p` `Q \<noteq> P`]  by  blast
	have "ray_on q p G" using `ray_on q p G \<and> seg_eq q G Q P` by blast
	obtain H where "ray_on q s H \<and> seg_eq q H Q S" using layoff[OF `q \<noteq> s` `Q \<noteq> S`]  by  blast
	have "ray_on q s H" using `ray_on q s H \<and> seg_eq q H Q S` by blast
	obtain K where "ray_on q r K \<and> seg_eq q K Q R" using layoff[OF `q \<noteq> r` `Q \<noteq> R`]  by  blast
	have "ray_on q r K" using `ray_on q r K \<and> seg_eq q K Q R` by blast
	have "seg_eq q K Q R" using `ray_on q r K \<and> seg_eq q K Q R` by blast
	have "ang_eq P Q S A B C" using equalanglessymmetric[OF `ang_eq A B C P Q S`] .
	have "ang_eq P Q S a b c" using equalanglestransitive[OF `ang_eq P Q S A B C` `ang_eq A B C a b c`] .
	have "ang_eq P Q S p q s" using equalanglestransitive[OF `ang_eq P Q S a b c` `ang_eq a b c p q s`] .
	have "ang_eq P Q S G q H" using equalangleshelper[OF `ang_eq P Q S p q s` `ray_on q p G` `ray_on q s H`] .
	have "ang_eq S Q R D E F" using equalanglessymmetric[OF `ang_eq D E F S Q R`] .
	have "ang_eq S Q R d e f" using equalanglestransitive[OF `ang_eq S Q R D E F` `ang_eq D E F d e f`] .
	have "ang_eq S Q R s q r" using equalanglestransitive[OF `ang_eq S Q R d e f` `ang_eq d e f s q r`] .
	have "ang_eq S Q R H q K" using equalangleshelper[OF `ang_eq S Q R s q r` `ray_on q s H` `ray_on q r K`] .
	have "\<not> col G q H" using equalanglesNC[OF `ang_eq P Q S G q H`] .
	have "seg_eq q G Q P" using `ray_on q p G \<and> seg_eq q G Q P` by blast
	have "seg_eq q H Q S" using `ray_on q s H \<and> seg_eq q H Q S` by blast
	have "ang_eq G q H P Q S" using equalanglessymmetric[OF `ang_eq P Q S G q H`] .
	have "seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P" using Prop04[OF `seg_eq q G Q P` `seg_eq q H Q S` `ang_eq G q H P Q S`] .
	have "seg_eq G H P S" using `seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P` by blast
	have "ang_eq q H G Q S P" using `seg_eq G H P S \<and> ang_eq q G H Q P S \<and> ang_eq q H G Q S P` by blast
	have "ang_eq H q K S Q R" using equalanglessymmetric[OF `ang_eq S Q R H q K`] .
	have "seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S" using Prop04[OF `seg_eq q H Q S` `seg_eq q K Q R` `ang_eq H q K S Q R`] .
	have "seg_eq H K S R" using `seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S` by blast
	have "ang_eq q H K Q S R" using `seg_eq H K S R \<and> ang_eq q H K Q S R \<and> ang_eq q K H Q R S` by blast
	have "ang_eq G H q P S Q" using equalanglesflip[OF `ang_eq q H G Q S P`] .
	have "Q = Q" using equalityreflexiveE.
	have "S \<noteq> Q" using NCdistinct[OF `\<not> col P Q S`] by blast
	have "ray_on S Q Q" using ray4 `Q = Q` `S \<noteq> Q` by blast
	have "supplement P S Q Q R" using supplement_b[OF `ray_on S Q Q` `bet P S R`] .
	have "ang_sum_right G H q q H K" using tworightangles_b[OF `supplement P S Q Q R` `ang_eq G H q P S Q` `ang_eq q H K Q S R`] .
	have "bet p s r" using `ang_eq a b c p q s \<and> ang_eq d e f s q r \<and> bet p s r` by blast
	have "col q s H" using rayimpliescollinear[OF `ray_on q s H`] .
	have "col q H s" using collinearorder[OF `col q s H`] by blast
	have "\<not> col G q H" using `\<not> col G q H` .
	have "col q p G" using rayimpliescollinear[OF `ray_on q p G`] .
	have "col G q p" using collinearorder[OF `col q p G`] by blast
	have "q = q" using equalityreflexiveE.
	have "col G q q" using collinear_b `q = q` by blast
	have "q \<noteq> p" using ray2[OF `ray_on q p G`] .
	have "p \<noteq> q" using inequalitysymmetric[OF `q \<noteq> p`] .
	have "\<not> col p q H" using NChelper[OF `\<not> col G q H` `col G q p` `col G q q` `p \<noteq> q`] .
	have "\<not> col q H p" using NCorder[OF `\<not> col p q H`] by blast
	have "oppo_side p q H r" using oppositeside_b[OF `bet p s r` `col q H s` `\<not> col q H p`] .
	have "oppo_side r q H p" using oppositesidesymmetric[OF `oppo_side p q H r`] .
	have "col q H q" using collinear_b `q = q` by blast
	have "ray_on q K r" using ray5[OF `ray_on q r K`] .
	have "oppo_side K q H p" using n9_5[OF `oppo_side r q H p` `ray_on q K r` `col q H q`] .
	have "oppo_side p q H K" using oppositesidesymmetric[OF `oppo_side K q H p`] .
	have "ray_on q G p" using ray5[OF `ray_on q p G`] .
	have "oppo_side G q H K" using n9_5[OF `oppo_side p q H K` `ray_on q G p` `col q H q`] .
	have "oppo_side K q H G" using oppositesidesymmetric[OF `oppo_side G q H K`] .
	have "q \<noteq> H" using raystrict[OF `ray_on q s H`] .
	have "H \<noteq> q" using inequalitysymmetric[OF `q \<noteq> H`] .
	have "ray_on H q q" using ray4 `q = q` `H \<noteq> q` by blast
	have "bet G H K" using Prop14[OF `ang_sum_right G H q q H K` `ray_on H q q` `oppo_side K q H G`] by blast
	have "seg_eq G K P R" using sumofparts[OF `seg_eq G H P S` `seg_eq H K S R` `bet G H K` `bet P S R`] .
	have "seg_eq q G Q P" using `seg_eq q G Q P` .
	have "seg_eq q K Q R" using `seg_eq q K Q R` .
	have "P = P" using equalityreflexiveE.
	have "R = R" using equalityreflexiveE.
	have "ray_on Q P P" using ray4 `P = P` `Q \<noteq> P` by blast
	have "ray_on Q R R" using ray4 `R = R` `Q \<noteq> R` by blast
	have "\<not> col P S Q" using NCorder[OF `\<not> col P Q S`] by blast
	have "col P S R" using collinear_b `ang_eq A B C P Q S \<and> ang_eq D E F S Q R \<and> bet P S R` by blast
	have "P = P" using equalityreflexiveE.
	have "col P S P" using collinear_b `P = P` by blast
	have "P \<noteq> R" using betweennotequal[OF `bet P S R`] by blast
	have "\<not> col P R Q" using NChelper[OF `\<not> col P S Q` `col P S P` `col P S R` `P \<noteq> R`] .
	have "\<not> col P Q R" using NCorder[OF `\<not> col P R Q`] by blast
	have "seg_eq Q P q G" using congruencesymmetric[OF `seg_eq q G Q P`] .
	have "seg_eq Q R q K" using congruencesymmetric[OF `seg_eq q K Q R`] .
	have "seg_eq P R G K" using congruencesymmetric[OF `seg_eq G K P R`] .
	have "ang_eq P Q R p q r" using equalangles_b[OF `ray_on Q P P` `ray_on Q R R` `ray_on q p G` `ray_on q r K` `seg_eq Q P q G` `seg_eq Q R q K` `seg_eq P R G K` `\<not> col P Q R`] .
	thus ?thesis by blast
qed

end