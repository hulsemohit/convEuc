theory angletrichotomy
	imports n3_7a Geometry Prop07 angleordertransitive betweennotequal collinear4 collinearorder congruenceflip inequalitysymmetric layoffunique ray3 rayimpliescollinear raystrict sameside2 samesidesymmetric
begin

theorem angletrichotomy:
	assumes "axioms"
		"ang_lt A B C D E F"
	shows "\<not> (ang_lt D E F A B C)"
proof -
	have "\<not> (ang_lt D E F A B C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (ang_lt D E F A B C))"
hence "ang_lt D E F A B C" by blast
		have "ang_lt A B C A B C" using angleordertransitive[OF `axioms` `ang_lt A B C D E F` `ang_lt D E F A B C`] .
		obtain G H J where "bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H" using anglelessthan_f[OF `axioms` `ang_lt A B C A B C`]  by  blast
		have "bet G H J" using `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
		have "ray_on B A G" using `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
		have "ray_on B C J" using `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
		have "ang_eq A B C A B H" using `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
		obtain U V u v where "ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C" using equalangles_f[OF `axioms` `ang_eq A B C A B H`]  by  blast
		have "ray_on B A U" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "ray_on B C V" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "ray_on B A u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "ray_on B H v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "seg_eq B U B u" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "seg_eq B V B v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "seg_eq U V u v" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "\<not> col A B C" using `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		have "\<not> (A = B)"
		proof (rule ccontr)
			assume "\<not> (A \<noteq> B)"
			hence "A = B" by blast
			have "col A B C" using collinear_b `axioms` `A = B` by blast
			show "False" using `col A B C` `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		qed
		hence "A \<noteq> B" by blast
		have "U = u" using layoffunique[OF `axioms` `ray_on B A U` `ray_on B A u` `seg_eq B U B u`] .
		have "seg_eq U V U v" using `seg_eq U V u v` `U = u` by blast
		have "col B A G" using rayimpliescollinear[OF `axioms` `ray_on B A G`] .
		have "G \<noteq> H" using betweennotequal[OF `axioms` `bet G H J`] by blast
		have "H \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> H`] .
		obtain P where "bet H G P \<and> seg_eq G P H G" using extensionE[OF `axioms` `H \<noteq> G` `H \<noteq> G`]  by  blast
		have "\<not> (col B A J)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B A J))"
hence "col B A J" by blast
			have "col B C J" using rayimpliescollinear[OF `axioms` `ray_on B C J`] .
			have "col J B A" using collinearorder[OF `axioms` `col B A J`] by blast
			have "col J B C" using collinearorder[OF `axioms` `col B C J`] by blast
			have "B \<noteq> J" using raystrict[OF `axioms` `ray_on B C J`] .
			have "J \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> J`] .
			have "col B A C" using collinear4[OF `axioms` `col J B A` `col J B C` `J \<noteq> B`] .
			have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
			show "False" using `col A B C` `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		qed
		hence "\<not> col B A J" by blast
		have "\<not> (col B U H)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B U H))"
hence "col B U H" by blast
			have "col B A U" using rayimpliescollinear[OF `axioms` `ray_on B A U`] .
			have "col U B A" using collinearorder[OF `axioms` `col B A U`] by blast
			have "col U B H" using collinearorder[OF `axioms` `col B U H`] by blast
			have "B \<noteq> U" using raystrict[OF `axioms` `ray_on B A U`] .
			have "U \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> U`] .
			have "col B A H" using collinear4[OF `axioms` `col U B A` `col U B H` `U \<noteq> B`] .
			have "col B A G" using `col B A G` .
			have "col A B G" using collinearorder[OF `axioms` `col B A G`] by blast
			have "col A B H" using collinearorder[OF `axioms` `col B A H`] by blast
			have "col B G H" using collinear4[OF `axioms` `col A B G` `col A B H` `A \<noteq> B`] .
			have "col G H B" using collinearorder[OF `axioms` `col B G H`] by blast
			have "col G H J" using collinear_b `axioms` `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
			have "G \<noteq> H" using betweennotequal[OF `axioms` `bet G H J`] by blast
			have "col H B J" using collinear4[OF `axioms` `col G H B` `col G H J` `G \<noteq> H`] .
			have "col H B A" using collinearorder[OF `axioms` `col A B H`] by blast
			have "\<not> (H \<noteq> B)"
			proof (rule ccontr)
				assume "\<not> (\<not> (H \<noteq> B))"
hence "H \<noteq> B" by blast
				have "col B J A" using collinear4[OF `axioms` `col H B J` `col H B A` `H \<noteq> B`] .
				have "col B A J" using collinearorder[OF `axioms` `col B J A`] by blast
				show "False" using `col B A J` `\<not> col B A J` by blast
			qed
			hence "H = B" by blast
			have "bet G B J" using `bet G H J` `H = B` by blast
			have "col G B J" using collinear_b `axioms` `bet G B J` by blast
			have "col B G J" using collinearorder[OF `axioms` `col G B J`] by blast
			have "col B G A" using collinearorder[OF `axioms` `col A B G`] by blast
			have "B \<noteq> G" using raystrict[OF `axioms` `ray_on B A G`] .
			have "col G J A" using collinear4[OF `axioms` `col B G J` `col B G A` `B \<noteq> G`] .
			have "col G J B" using collinearorder[OF `axioms` `col B G J`] by blast
			have "G \<noteq> J" using betweennotequal[OF `axioms` `bet G B J`] by blast
			have "col J A B" using collinear4[OF `axioms` `col G J A` `col G J B` `G \<noteq> J`] .
			have "col B A J" using collinearorder[OF `axioms` `col J A B`] by blast
			have "\<not> col B A J" using `\<not> col B A J` .
			show "False" using `\<not> col B A J` `col B A J` by blast
		qed
		hence "\<not> col B U H" by blast
		have "ray_on B A U" using `ray_on B A U` .
		have "ray_on B A G" using `ray_on B A G` .
		have "ray_on B G U" using ray3[OF `axioms` `ray_on B A G` `ray_on B A U`] .
		have "col B G U" using rayimpliescollinear[OF `axioms` `ray_on B G U`] .
		have "col B U G" using collinearorder[OF `axioms` `col B G U`] by blast
		have "bet H G P" using `bet H G P \<and> seg_eq G P H G` by blast
		have "bet J H G" using betweennesssymmetryE[OF `axioms` `bet G H J`] .
		have "bet J G P" using n3_7a[OF `axioms` `bet J H G` `bet H G P`] .
		have "\<not> col B U H" using `\<not> col B U H` .
		have "\<not> (col B U J)"
		proof (rule ccontr)
			assume "\<not> (\<not> (col B U J))"
hence "col B U J" by blast
			have "col B C J" using rayimpliescollinear[OF `axioms` `ray_on B C J`] .
			have "col B J C" using collinearorder[OF `axioms` `col B C J`] by blast
			have "col B A U" using rayimpliescollinear[OF `axioms` `ray_on B A U`] .
			have "col U B A" using collinearorder[OF `axioms` `col B A U`] by blast
			have "col U B J" using collinearorder[OF `axioms` `col B U J`] by blast
			have "B \<noteq> U" using raystrict[OF `axioms` `ray_on B A U`] .
			have "U \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> U`] .
			have "col B A J" using collinear4[OF `axioms` `col U B A` `col U B J` `U \<noteq> B`] .
			have "col J B C" using collinearorder[OF `axioms` `col B C J`] by blast
			have "col J B A" using collinearorder[OF `axioms` `col B A J`] by blast
			have "B \<noteq> J" using raystrict[OF `axioms` `ray_on B C J`] .
			have "J \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> J`] .
			have "col B C A" using collinear4[OF `axioms` `col J B C` `col J B A` `J \<noteq> B`] .
			have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
			show "False" using `col A B C` `ray_on B A U \<and> ray_on B C V \<and> ray_on B A u \<and> ray_on B H v \<and> seg_eq B U B u \<and> seg_eq B V B v \<and> seg_eq U V u v \<and> \<not> col A B C` by blast
		qed
		hence "\<not> col B U J" by blast
		have "same_side J H B U" using sameside_b[OF `axioms` `col B U G` `col B U G` `bet J G P` `bet H G P` `\<not> col B U J` `\<not> col B U H`] .
		have "same_side H J B U" using samesidesymmetric[OF `axioms` `same_side J H B U`] by blast
		have "ray_on B J V" using ray3[OF `axioms` `ray_on B C J` `ray_on B C V`] .
		have "B = B" using equalityreflexiveE[OF `axioms`] .
		have "col B B U" using collinear_b `axioms` `B = B` by blast
		have "same_side H V B U" using sameside2[OF `axioms` `same_side H J B U` `col B B U` `ray_on B J V`] .
		have "same_side V H B U" using samesidesymmetric[OF `axioms` `same_side H V B U`] by blast
		have "same_side V v B U" using sameside2[OF `axioms` `same_side V H B U` `col B B U` `ray_on B H v`] .
		have "B \<noteq> U" using raystrict[OF `axioms` `ray_on B A U`] .
		have "seg_eq V B v B" using congruenceflip[OF `axioms` `seg_eq B V B v`] by blast
		have "seg_eq V U v U" using congruenceflip[OF `axioms` `seg_eq U V U v`] by blast
		have "V = v" using Prop07[OF `axioms` `B \<noteq> U` `seg_eq V B v B` `seg_eq V U v U` `same_side V v B U`] .
		have "ray_on B H V" using `ray_on B H v` `V = v` by blast
		have "col B H V" using rayimpliescollinear[OF `axioms` `ray_on B H V`] .
		have "col B J V" using rayimpliescollinear[OF `axioms` `ray_on B J V`] .
		have "col V B J" using collinearorder[OF `axioms` `col B J V`] by blast
		have "col V B H" using collinearorder[OF `axioms` `col B H V`] by blast
		have "B \<noteq> V" using raystrict[OF `axioms` `ray_on B C V`] .
		have "V \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> V`] .
		have "col B J H" using collinear4[OF `axioms` `col V B J` `col V B H` `V \<noteq> B`] .
		have "col G H J" using collinear_b `axioms` `bet G H J \<and> ray_on B A G \<and> ray_on B C J \<and> ang_eq A B C A B H` by blast
		have "col H J B" using collinearorder[OF `axioms` `col B J H`] by blast
		have "col H J G" using collinearorder[OF `axioms` `col G H J`] by blast
		have "J \<noteq> H" using betweennotequal[OF `axioms` `bet J H G`] by blast
		have "H \<noteq> J" using inequalitysymmetric[OF `axioms` `J \<noteq> H`] .
		have "col J B G" using collinear4[OF `axioms` `col H J B` `col H J G` `H \<noteq> J`] .
		have "col B C J" using rayimpliescollinear[OF `axioms` `ray_on B C J`] .
		have "col J B C" using collinearorder[OF `axioms` `col B C J`] by blast
		have "B \<noteq> J" using raystrict[OF `axioms` `ray_on B C J`] .
		have "J \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> J`] .
		have "col B G C" using collinear4[OF `axioms` `col J B G` `col J B C` `J \<noteq> B`] .
		have "col G B C" using collinearorder[OF `axioms` `col B G C`] by blast
		have "col B A G" using rayimpliescollinear[OF `axioms` `ray_on B A G`] .
		have "col G B A" using collinearorder[OF `axioms` `col B A G`] by blast
		have "B \<noteq> G" using raystrict[OF `axioms` `ray_on B A G`] .
		have "G \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> G`] .
		have "col B C A" using collinear4[OF `axioms` `col G B C` `col G B A` `G \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B C A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> (ang_lt D E F A B C)" by blast
	thus ?thesis by blast
qed

end