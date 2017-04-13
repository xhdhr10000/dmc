#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

struct Point {
	double x, y;
};

struct Tree {
	struct Point sp, ep;
	int si, ei;
	int li, ri;
	int level;
	double w;
};

int lp[2] = {10, 10}, lt[2], cp[2] = {0, 0}, ct[2] = {0, 0};
struct Point *points[2];
struct Tree *tree[2];
double Cz;
int n;
int DEBUG = 0;

void help() {
	printf("dmc\n");
	printf("Usage:\n");
	printf("\tdmc [input file 1] [input file 2] [σz] [n]");
}

double l(struct Point s, struct Point e) {
	return sqrt((s.x-e.x)*(s.x-e.x) + (s.y-e.y)*(s.y-e.y));
}

double d(struct Point s, struct Point e, struct Point c) {
	double lCurve  = l(c, s);
	double rCurve  = l(c, e);
	double seCurve = l(s, e);
	double cosTheta = (lCurve*lCurve + seCurve*seCurve - rCurve*rCurve) / (2*lCurve*seCurve);
	double d = lCurve * ((1-cosTheta > 0.0000001) ? sqrt(1-cosTheta*cosTheta) : 1);
	if (DEBUG) {
		printf("s(%.6lf %.6lf) e(%.6lf %.6lf) c(%.6lf %.6lf)\n", s.x, s.y, e.x, e.y, c.x, c.y);
		printf("lCurve=%.6lf rCurve=%.6lf seCurve=%.6lf cosTheta=%.6lf d=%.6lf\n", lCurve, rCurve, seCurve, cosTheta, d);
	}
	return d;
}

void split(int t, int idx) {
	if (tree[t][idx].ei - tree[t][idx].si == 1) return;

	double maxd = -1;
	int maxp;
	for (int i=tree[t][idx].si+1; i<tree[t][idx].ei; i++) {
		double dc = d(tree[t][idx].sp, tree[t][idx].ep, points[t][i]);
		if (DEBUG) printf("idx=%d i=%d d=%.6lf\n", idx, i, dc);
		if (dc > maxd) {
			maxd = dc;
			maxp = i;
		}
	}
	double ll = l(tree[t][idx].sp, points[t][maxp]);
	double lr = l(points[t][maxp], tree[t][idx].ep);

	if (ct[t] >= lt[t]) {
		lt[t] *= 2;
		tree[t] = (struct Tree*) realloc(tree[t], lt[t] * sizeof(struct Tree));
	}
	tree[t][ct[t]].sp = tree[t][idx].sp;
	tree[t][ct[t]].ep = points[t][maxp];
	tree[t][ct[t]].si = tree[t][idx].si;
	tree[t][ct[t]].ei = maxp;
	tree[t][ct[t]].li = -1;
	tree[t][ct[t]].ri = -1;
	tree[t][ct[t]].level = tree[t][idx].level + 1;
	tree[t][ct[t]].w = ll / (ll + lr) * tree[t][idx].w;
	tree[t][idx].li = ct[t];
	ct[t]++;
	tree[t][ct[t]].sp = points[t][maxp];
	tree[t][ct[t]].ep = tree[t][idx].ep;
	tree[t][ct[t]].si = maxp;
	tree[t][ct[t]].ei = tree[t][idx].ei;
	tree[t][ct[t]].li = -1;
	tree[t][ct[t]].ri = -1;
	tree[t][ct[t]].level = tree[t][idx].level + 1;
	tree[t][ct[t]].w = lr / (ll + lr) * tree[t][idx].w;
	tree[t][idx].ri = ct[t];
	ct[t]++;
}

double *u, *um, uw = 0;
struct Point *ump[2];

int equal(struct Point p1, struct Point p2) {
	return (fabs(p1.x - p2.x) < 0.0000001 && fabs(p1.y - p2.y) < 0.0000001);
}

double calU(struct Point left, struct Point right, struct Point child1, struct Point *child2, int level) {
	double a1 = l(left, child1), a2 = (child2 == NULL) ? 0 : l(left, *child2);
	double b = l(left, right);
	double c1 = l(child1, right), c2 = (child2 == NULL) ? 0 : l(*child2, right);
	double cosTheta1_1 = (a1*a1 + b*b - c1*c1) / (2*a1*b);
	double cosTheta1_2 = (c1*c1 + b*b - a1*a1) / (2*c1*b);
	double cosTheta2_1 = (child2 == NULL) ? 0 : (a2*a2 + b*b - c2*c2) / (2*a2*b);
	double cosTheta2_2 = (child2 == NULL) ? 0 : (c2*c2 + b*b - a2*a2) / (2*c2*b);
	if (cosTheta1_1 < 0 || cosTheta1_2 < 0 || (child2 != NULL && (cosTheta2_1 < 0 || cosTheta2_2 < 0))) {
		/* fixme: error */
		return -1;
	}
	double sinTheta1_1 = (1-cosTheta1_1 < 0.0000001)? 0: sin(acos(cosTheta1_1));
	double sinTheta1_2 = (1-cosTheta1_2 < 0.0000001)? 0: sin(acos(cosTheta1_2));
	double sinTheta2_1 = (child2 == NULL)? 0: (1-cosTheta2_1 < 0.0000001)? 0: sin(acos(cosTheta2_1));
	double sinTheta2_2 = (child2 == NULL)? 0: (1-cosTheta2_2 < 0.0000001)? 0: sin(acos(cosTheta2_2));
	if (DEBUG) {
		printf("acos1=%lf sin1=%lf\n", acos(cosTheta1_1), sin(acos(cosTheta1_1)));
		printf("left(%.6lf %.6lf) right(%.6lf %.6lf) child1(%.6lf %.6lf) child2(%.6lf %.6lf)\n",
			left.x, left.y, right.x, right.y, child1.x, child1.y,
			(child2 != NULL)?child2->x:-1, (child2 != NULL)?child2->y:-1);
		printf("a1=%lf a2=%lf b=%lf c1=%lf c2=%lf cos1_1=%lf cos1_2=%lf cos2_1=%lf cos2_2=%lf sin1_1=%lf sin1_2=%lf sin2_1=%lf sin2_2=%lf\n",
			a1, a2, b, c1, c2, cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2, 
			sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2);
	}

	double sumR = 0;
	double step = (right.x - left.x) / n;
	for (double x=left.x; x<right.x; x+=step) {
		struct Point p1, p2;
		p1.x = x;
		if (p1.x < child1.x)
			p1.y = (child1.y-left.y)/(child1.x-left.x)*x + (child1.x*left.y - left.x*child1.y)/(child1.x - left.x);
		else
			p1.y = (right.y-child1.y)/(right.x-child1.x)*x + (right.y*child1.x - child1.y*right.x)/(child1.x - right.x);
		if (child2 != NULL) {
			p2.x = x;
			if (p2.x < child2->x)
				p2.y = (child2->y-left.y)/(child2->x-left.x)*x + (child2->x*left.y - left.x*child2->y)/(child2->x - left.x);
			else
				p2.y = (right.y-child2->y)/(right.x-child2->x)*x + (right.y*child2->x - child2->y*right.x)/(child2->x - right.x);
		}

		double d1 = (p1.x < child1.x) ? l(p1, left) : l(p1, right);
		double d2 = (child2 != NULL) ? ((p1.x < child2->x) ? l(p2, left) : l(p2, right)) : 0;
		double dd1 = (p1.x < child1.x) ? d1/a1 : d1/c1;
		double dd2 = (child2 != NULL) ? ((p2.x < child2->x) ? d2/a2 : d2/c2) : 0;
		double r1 = sqrt(1 - 2*dd1 + 2*dd1*dd1) * Cz;
		double r2 = (child2 != NULL) ? sqrt(1 - 2*dd2 + 2*dd2*dd2) * Cz : 0;
		double R = ((p1.x < child1.x) ? d1*sinTheta1_1 : d1*sinTheta1_2)
		+ ((child2 != NULL) ? ((p2.x < child2->x) ? d2*sinTheta2_1 : d2*sinTheta2_2) : 0)
		+ r1 + r2;
		sumR += R;
		if (R > um[level]) {
			um[level] = R;
			ump[0][level] = p1;
			ump[1][level] = p2;
		}
		if (DEBUG) printf("R: x=%.6lf d1=%.6lf d2=%.6f r1=%.6lf r2=%.6f R=%.6lf sumR=%.6lf\n", x, d1, d2, r1, r2, R, sumR);
	}
	return sumR / n;
}

void qualityAssessment(struct Tree t1, struct Tree t2) {
	if (t1.li == -1 && t2.li == -1) return;
	if (t1.li != -1 && t2.li == -1) {
		/* case 2.1 with t1 */
		struct Point left  = (t1.sp.x < t1.ep.x) ? t1.sp : t1.ep;
		struct Point right = (t1.sp.x < t1.ep.x) ? t1.ep : t1.sp;
		struct Point child = tree[0][t1.li].ep;
		double U = calU(left, right, child, NULL, t1.level);
		u[t1.level] += U;
		uw += U * t1.w;
	} else if (t1.li == -1 && t2.li != -1) {
		/* case 2.1 with t2 */
		struct Point left  = (t2.sp.x < t2.ep.x) ? t2.sp : t2.ep;
		struct Point right = (t2.sp.x < t2.ep.x) ? t2.ep : t2.sp;
		struct Point child = tree[1][t2.li].ep;
		double U = calU(left, right, child, NULL, t1.level);
		u[t2.level] += U;
		uw += U * t2.w;
	} else {
		if (equal(tree[0][t1.li].sp, tree[1][t2.li].sp) && 
			equal(tree[0][t1.li].ep, tree[1][t2.li].ep) &&
			equal(tree[0][t1.ri].sp, tree[1][t2.ri].sp) &&
			equal(tree[0][t1.ri].ep, tree[1][t2.ri].ep)) 
		{
			qualityAssessment(tree[0][t1.li], tree[1][t2.li]);
			qualityAssessment(tree[0][t1.ri], tree[1][t2.ri]);
		} else {
			/* case 2.2 */
			struct Point left  = (t1.sp.x < t1.ep.x) ? t1.sp : t1.ep;
			struct Point right = (t1.sp.x < t1.ep.x) ? t1.ep : t1.sp;
			struct Point child1 = tree[0][t1.li].ep;
			struct Point child2 = tree[1][t2.li].ep;
			double U = calU(left, right, child1, &child2, t1.level);
			u[t1.level] += U;
			uw += U * t1.w;
		}
	}
}

int main(int argc, char **argv) {
	if (argc <= 4) {
		help();
		return 0;
	}
	FILE *fin[2] = { fopen(argv[1], "r"), fopen(argv[2], "r") };
	Cz = atof(argv[3]);
	n = atoi(argv[4]);
	if (argc > 5) DEBUG = 1;

	for (int i=0; i<2; i++) {
		points[i] = (struct Point*) malloc(lp[i] * sizeof(struct Point));

		while (!feof(fin[i])) {
			if (fscanf(fin[i], "%lf%lf", &points[i][cp[i]].x, &points[i][cp[i]].y) == -1) break;
			cp[i]++;
			if (cp[i] >= lp[i]) {
				lp[i] *= 2;
				points[i] = (struct Point*) realloc(points[i], lp[i] * sizeof(struct Point));
			}
		}

		if (DEBUG) {
			for (int j=0; j<cp[i]; j++) {
				printf("%.6f %.6f\n", points[i][j].x, points[i][j].y);
			}
		}

		lt[i] = cp[i] * 2;
		tree[i] = (struct Tree*) malloc(lt[i] * sizeof(struct Tree));
		tree[i][0].sp = points[i][0];
		tree[i][0].ep = points[i][cp[i]-1];
		tree[i][0].si = 0;
		tree[i][0].ei = cp[i]-1;
		tree[i][0].li = -1;
		tree[i][0].ri = -1;
		tree[i][0].level = 0;
		tree[i][0].w = 1;
		ct[i]++;
		int h = 0;
		while (h < ct[i]) {
			split(i, h++);
		}

		printf("\n------------------------------ Tree %d ------------------------------\n", i);
		for (int j=0; j<ct[i]; j++) {
			printf("idx=%d sp(%.6lf %.6lf) ep(%.6lf %.6lf) si=%d ei=%d li=%d ri=%d level=%d w=%.6lf\n",
				j, tree[i][j].sp.x, tree[i][j].sp.y, tree[i][j].ep.x, tree[i][j].ep.y,
				tree[i][j].si, tree[i][j].ei, tree[i][j].li, tree[i][j].ri, tree[i][j].level, tree[i][j].w);
		}
	}

	int len = MAX(tree[0][ct[0]-1].level, tree[1][ct[1]-1].level) + 1;
	u = (double*) malloc(len * sizeof(double));
	um = (double*) malloc(len * sizeof(double));
	ump[0] = (struct Point*) malloc(len * sizeof(struct Point));
	ump[1] = (struct Point*) malloc(len * sizeof(struct Point));
	memset(u, 0, len * sizeof(double));
	memset(um, 0, len * sizeof(double));
	qualityAssessment(tree[0][0], tree[1][0]);

	printf("\n------------------------------ Output ------------------------------\n");
	for (int i=0; i<=tree[0][ct[0]-1].level; i++) {
		if (u[i] != 0) {
			printf("level=%d U=%.6lf Umax=%.6lf Umax at:\n", i, u[i], um[i]);
			printf("\tp1(%.6lf %.6lf) p2(%.6lf %.6lf)\n", ump[0][i].x, ump[0][i].y, ump[1][i].x, ump[1][i].y);
		}
	}
	printf("AU(Curve)=%.6f\n", uw);

	for (int i=0; i<2; i++) {
		free(points[i]);
		free(tree[i]);
	}
	return 0;
}