theory equalanglestransitive
	imports Axioms Definitions Theorems
begin

theorem equalanglestransitive:
	assumes: `axioms`
		"ang_eq A B C D E F"
		"ang_eq D E F P Q R"
	shows: "ang_eq A B C P Q R"
proof -
	have "A \<noteq> B" using angledistinct[OF `axioms` `ang_eq A B C D E F`] by blast
	have "D \<noteq> E" using angledistinct[OF `axioms` `ang_eq A B C D E F`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "E \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> E`] .
	have "E \<noteq> F" using angledistinct[OF `axioms` `ang_eq A B C D E F`] by blast
	have "B \<noteq> C" using angledistinct[OF `axioms` `ang_eq A B C D E F`] by blast
	have "P \<noteq> Q" using angledistinct[OF `axioms` `ang_eq D E F P Q R`] by blast
	have "Q \<noteq> P" using inequalitysymmetric[OF `axioms` `P \<noteq> Q`] .
	obtain U where "ray_on E D U \<and> seg_eq E U B A" using layoff[OF `axioms` `E \<noteq> D` `B \<noteq> A`]  by  blast
	obtain V where "ray_on E F V \<and> seg_eq E V B C" using layoff[OF `axioms` `E \<noteq> F` `B \<noteq> C`]  by  blast
	have "ray_on E D U" using `ray_on E D U \<and> seg_eq E U B A` by blast
	have "ray_on E F V" using `ray_on E F V \<and> seg_eq E V B C` by blast
	have "E \<noteq> U" using raystrict[OF `axioms` `ray_on E D U`] .
	have "E \<noteq> V" using raystrict[OF `axioms` `ray_on E F V`] .
	have "ang_eq P Q R D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F P Q R`] .
	have "Q \<noteq> R" using angledistinct[OF `axioms` `ang_eq D E F P Q R`] by blast
	obtain u where "ray_on Q P u \<and> seg_eq Q u E U" using layoff[OF `axioms` `Q \<noteq> P` `E \<noteq> U`]  by  blast
	obtain v where "ray_on Q R v \<and> seg_eq Q v E V" using layoff[OF `axioms` `Q \<noteq> R` `E \<noteq> V`]  by  blast
	have "seg_eq E U B A" using `ray_on E D U \<and> seg_eq E U B A` by blast
	have "seg_eq E V B C" using `ray_on E F V \<and> seg_eq E V B C` by blast
	have "ray_on Q P u" using `ray_on Q P u \<and> seg_eq Q u E U` by blast
	have "ray_on Q R v" using `ray_on Q R v \<and> seg_eq Q v E V` by blast
	have "seg_eq Q u E U" using `ray_on Q P u \<and> seg_eq Q u E U` by blast
	have "seg_eq Q v E V" using `ray_on Q R v \<and> seg_eq Q v E V` by blast
	have "\<not> col A B C" sorry
	have "ang_eq A B C D E F" using `ang_eq A B C D E F` .
	have "ray_on E D U" using `ray_on E D U` .
	have "ray_on E F V" using `ray_on E F V` .
	have "ang_eq A B C U E V" using equalangleshelper[OF `axioms` `ang_eq A B C D E F` `ray_on E D U` `ray_on E F V`] .
	have "seg_eq B A E U" using congruencesymmetric[OF `axioms` `seg_eq E U B A`] .
	have "seg_eq B C E V" using congruencesymmetric[OF `axioms` `seg_eq E V B C`] .
	have "seg_eq A C U V \<and> ang_eq B A C E U V \<and> ang_eq B C A E V U" using Prop04[OF `axioms` `seg_eq B A E U` `seg_eq B C E V` `ang_eq A B C U E V`] .
	have "seg_eq A C U V" using `seg_eq A C U V \<and> ang_eq B A C E U V \<and> ang_eq B C A E V U` by blast
	have "seg_eq E U Q u" using congruencesymmetric[OF `axioms` `seg_eq Q u E U`] .
	have "seg_eq E V Q v" using congruencesymmetric[OF `axioms` `seg_eq Q v E V`] .
	have "ang_eq D E F u Q v" using equalangleshelper[OF `axioms` `ang_eq D E F P Q R` `ray_on Q P u` `ray_on Q R v`] .
	have "ang_eq u Q v D E F" using equalanglessymmetric[OF `axioms` `ang_eq D E F u Q v`] .
	have "ang_eq u Q v U E V" using equalangleshelper[OF `axioms` `ang_eq u Q v D E F` `ray_on E D U` `ray_on E F V`] .
	have "ang_eq U E V u Q v" using equalanglessymmetric[OF `axioms` `ang_eq u Q v U E V`] .
	have "seg_eq U V u v \<and> ang_eq E U V Q u v \<and> ang_eq E V U Q v u" using Prop04[OF `axioms` `seg_eq E U Q u` `seg_eq E V Q v` `ang_eq U E V u Q v`] .
	have "seg_eq U V u v" using `seg_eq U V u v \<and> ang_eq E U V Q u v \<and> ang_eq E V U Q v u` by blast
	have "seg_eq A C u v" using congruencetransitive[OF `axioms` `seg_eq A C U V` `seg_eq U V u v`] .
	have "seg_eq B A Q u" using congruencetransitive[OF `axioms` `seg_eq B A E U` `seg_eq E U Q u`] .
	have "seg_eq B C Q v" using congruencetransitive[OF `axioms` `seg_eq B C E V` `seg_eq E V Q v`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "ang_eq A B C P Q R" sorry
	thus ?thesis by blast
qed

end