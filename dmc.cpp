#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define MAXINT 2147483647

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
double n;
int DEBUG = 0;

void help() {
	printf("Usage: dmc [input file 1] [input file 2] [Cz] [n]\n");
	printf("Parameters:\n");
	printf("   input file 1: the first input file\n");
	printf("   input file 2: the second input file\n");
	printf("   Cz:           the error of points, which is a constant\n");
	printf("   n:            segment length, divide each segment to several n-lengthed segments\n");
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
struct Point *ump;

int equal(double d1, double d2) {
	return (fabs(d1 - d2) < 0.0000001);
}

int equal(struct Point p1, struct Point p2) {
	return (equal(p1.x, p2.x) && equal(p1.y, p2.y));
}

double calR(double len, struct Point left, struct Point right, struct Point child1, struct Point *child2,
	double a1, double a2, double c1, double c2,
	double sinTheta1_1, double sinTheta1_2, double sinTheta2_1, double sinTheta2_2,
	double cosTheta1_1, double cosTheta1_2, double cosTheta2_1, double cosTheta2_2) {
	double R = 0, d1, dd1, d2, dd2, r1, r2 = 0;
	if (len / cosTheta1_1 < l(left, child1)) {
		d1 = len / cosTheta1_1;
		dd1 = d1 / a1;
		R += d1 * sinTheta1_1;
	} else {
		d1 = (l(left, right)-len) / cosTheta1_2;
		dd1 = d1 / c1;
		R += d1 * sinTheta1_2;
	}
	r1 = sqrt(1 - 2*dd1 + 2*dd1*dd1) * Cz;
	R += r1;
	if (child2 != NULL) {
		if (len / cosTheta2_1 < l(left, *child2)) {
			d2 = len / cosTheta2_1;
			dd2 = d2 / a2;
			R += d2 * sinTheta2_1;
		} else {
			d2 = (l(left, right)-len) / cosTheta2_2;
			dd2 = d2 / c2;
			R += d2 * sinTheta2_2;
		}
		r2 = sqrt(1 - 2*dd2 + 2*dd2*dd2) * Cz;
		R += r2;
	}
	if (DEBUG) printf("R: l=%.6lf d1=%.6lf d2=%.6f r1=%.6lf r2=%.6f R=%.6lf\n", len, d1, d2, r1, r2, R);

	return R;
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
	double sinTheta1_1 = equal(cosTheta1_1, 1)? 0: sin(acos(cosTheta1_1));
	double sinTheta1_2 = equal(cosTheta1_2, 1)? 0: sin(acos(cosTheta1_2));
	double sinTheta2_1 = (child2 == NULL)? 0: equal(cosTheta2_1, 1)? 0: sin(acos(cosTheta2_1));
	double sinTheta2_2 = (child2 == NULL)? 0: equal(cosTheta2_2, 1)? 0: sin(acos(cosTheta2_2));
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
	int count = 0;
	double len = 0;
	struct Point p;
	p.x = left.x;
	p.y = left.y;
	if (equal(left.x, right.x)) {
		/* perpendicular to x-axis */
		p.x = left.x;
		p.y = left.y;
		while (p.y < right.y) {
			len += n;
			p.y += n;
			double R = calR(len, left, right, child1, child2, a1, a2, c1, c2,
				sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
				cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
			sumR += R;
			count++;

			if (R > um[level]) {
				um[level] = R;
				ump[level] = p;
			}
		}
	} else {
		double k = (right.y - left.y) / (right.x - left.x);
		if (equal(k, 0)) {
			/* perpendicular to y-axis */
			while (p.x < right.x) {
				len += n;
				p.x += n;
				double R = calR(len, left, right, child1, child2, a1, a2, c1, c2,
					sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
					cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
				sumR += R;
				count++;

				if (R > um[level]) {
					um[level] = R;
					ump[level] = p;
				}
			}
		} else {
			double b = left.y - k*left.x;
			double x0 = (right.x*left.y - left.x*right.y) / (left.y - right.y);
			double sinAlpha = sin(atan(k));
			if (DEBUG) printf("k=%lf sinAlpha=%lf\n", k, sinAlpha);
			while (p.x < right.x) {
				len += n;
				p.y += n * sinAlpha;
				p.x = (p.y - b) / k;

				double R = calR(len, left, right, child1, child2, a1, a2, c1, c2,
					sinTheta1_1, sinTheta1_2, sinTheta2_1, sinTheta2_2,
					cosTheta1_1, cosTheta1_2, cosTheta2_1, cosTheta2_2);
				sumR += R;
				count++;

				if (R > um[level]) {
					um[level] = R;
					ump[level] = p;
				}
			}
		}
	}
	return sumR / count;
}

void qualityAssessment(struct Tree t1, struct Tree t2) {
	if (t1.li == -1 && t2.li == -1) return;
	if (t1.li != -1 && t2.li == -1) {
		/* case 2.1 with t1 */
		struct Point left  = equal(t1.sp.x, t1.ep.x)? 
		((t1.sp.y < t1.ep.y)? t1.sp: t1.ep): 
		((t1.sp.x < t1.ep.x)? t1.sp: t1.ep);
		struct Point right = equal(t1.sp.x, t1.ep.x)?
		((t1.sp.y < t1.ep.y)? t1.ep: t1.sp):
		((t1.sp.x < t1.ep.x)? t1.ep: t1.sp);
		struct Point child = tree[0][t1.li].ep;
		double U = calU(left, right, child, NULL, t1.level);
		u[t1.level] += U;
		uw += U * t1.w;
	} else if (t1.li == -1 && t2.li != -1) {
		/* case 2.1 with t2 */
		struct Point left  = equal(t2.sp.x, t2.ep.x)?
		((t2.sp.y < t2.ep.y)? t2.sp: t2.ep):
		((t2.sp.x < t2.ep.x)? t2.sp: t2.ep);
		struct Point right = equal(t2.sp.x, t2.ep.x)?
		((t2.sp.y < t2.ep.y)? t2.ep: t2.sp):
		((t2.sp.x < t2.ep.x)? t2.ep: t2.sp);
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
			struct Point left  = equal(t1.sp.x, t1.ep.x)?
			((t1.sp.y < t1.ep.y)? t1.sp: t1.ep):
			((t1.sp.x < t1.ep.x)? t1.sp: t1.ep);
			struct Point right = equal(t1.sp.x, t1.ep.x)?
			((t1.sp.y < t1.ep.y)? t1.ep: t1.sp):
			((t1.sp.x < t1.ep.x)? t1.ep: t1.sp);
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
	n = atof(argv[4]);
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
	ump = (struct Point*) malloc(len * sizeof(struct Point));
	memset(u, 0, len * sizeof(double));
	memset(um, 0, len * sizeof(double));
	qualityAssessment(tree[0][0], tree[1][0]);

	printf("\n------------------------------ Output ------------------------------\n");
	for (int i=0; i<=tree[0][ct[0]-1].level; i++) {
		if (u[i] != 0) {
			printf("level=%d U=%.6lf Umax=%.6lf Umax at:\n", i, u[i], um[i]);
			printf("\tp(%.6lf %.6lf)\n", ump[i].x, ump[i].y);
		}
	}
	printf("AU(Curve)=%.6f\n", uw);

	for (int i=0; i<2; i++) {
		free(points[i]);
		free(tree[i]);
	}
	return 0;
}