
public class HydroTargetCoeffs2 {

    /*
    Simulation of hydrodynamic interactions following the algorithm of Hernandez-Ortiz et al. J. Chem. Phys. (2006)
    This class contains the codes for computing the target of flow terms
    Reminder: the flow is v_k(r_target) = sum_sources sum_q c_{k,i}(r_target,q,b) a_{i,j}(r_source,q,b) f_j
    with b = (z_target<z_source) the boolean indicating whether the target is below the source
    This computes the c_{k,i}(r_t,q,b) coefficients and can compute v_k(r_target)
    given lambda = sum_sources sum_q a_{i,j}(r_source,q,b) f_j
     */

    // static quantities (fixed for a simulation)

    static private double PI=Math.PI;

    static private double h,L,q[],q2[],K[],lij[],mij[],l2ij[],m2ij[],lmij[];

    static private int nk,nk2;


    // sin approx
    static double w0;
    static double PIo2= Math.PI/2;
    static double twoPI = 2*Math.PI;
    static double[] cosWave;
    static double[] dcosWave;

    // exp approx
    static double[] expX;
    static double[] dexpX;
    static double max;
    static double dx;

    static void setConditions(double h0,double L0, int n0) {
        h = h0;
        nk = n0;
        L=L0;
        nk2=nk*nk;

        // compute wave numbers
        q = new double[nk];
        q2 = new double[nk];
        K = new double[nk2];
        lij = new double[nk2];
        mij = new double[nk2];
        l2ij = new double[nk2];
        m2ij = new double[nk2];
        lmij = new double[nk2];
        for (int i = 0; i < nk; i++) {
            q[i] = (2 * i - (nk - 1)) * PI / L;  // symmetric qs, nk odd
            //q[i] = (2*i)*PI/L;
            q2[i] = q[i] * q[i];
        }
        for (int i = 0; i < nk; i++) {
            for (int j = 0; j < nk; j++) {
                K[i*nk+j] = Math.sqrt(q[i] * q[i] + q[j] * q[j]);
                lij[i*nk+j] = q[i];
                mij[i*nk+j] = q[j];
                l2ij[i*nk+j] = q2[i];
                m2ij[i*nk+j] = q2[j];
                lmij[i*nk+j] = q[i]*q[j];
            }
        }
        // sin, cos and exp functions are approximated for increasing the speed of the algorithm
        setWave();
        setExp();
    }

    // sine approximation for speed
    static private void setWave(){

        w0 = 10000/(twoPI);
        cosWave = new double[10001];
        dcosWave = new double[10001];
        for(int i=0;i<10001;i++){
            cosWave[i] = Math.cos( i / w0) ; // [0 PI]
            dcosWave[i] = Math.cos( (i+1) / w0)-  Math.cos(i / w0);
        }

    }

    static private double cos_apx(double x){

        double xc = (abs(x*w0)% 10000);

        int i = (int) Math.floor(xc);

        return cosWave[i] + (xc-i) * dcosWave[i];

    }

    static private double sin_apx(double x){

        return cos_apx(x-PIo2);

    }

    static private double abs(double x){
        return (x)<0.0?-x:x;
    }

    // exponential approximation for speed
    static private void setExp(){

        max = 3*nk*PI*h/L;
        dx = 100000/(2*max);

        expX = new double[100001];
        dexpX = new double[100001];
        for(int i=0;i<100001;i++){
            expX[i] = Math.exp( -max+i/dx) ; // [0 PI]
            dexpX[i] = ( Math.exp( -max+(i+1)/dx) -  expX[i] )  ;

        }

    }

    static private double exp_apx(double x){

        double xc = (x+max)*dx;
        int i = (int)Math.floor( xc );

        return expX[i] + (xc-i)*dexpX[i] ;

    }

    // Instantiated quantities (depend on the target)

    private double xp3,ck0_1;

    private double[][]  C_l2,C_m2,C_k2,C_l,C_m,C_lm;

    private double[] coskx,sinkx;

    private double[]  ck0_2;

    // constructor
    HydroTargetCoeffs2(){
        coskx = new double[nk2];
        sinkx = new double[nk2];

        C_l2 = new double[2][nk2];
        C_lm = new double[2][nk2];
        C_l  = new double[2][nk2];
        C_m2 = new double[2][nk2];
        C_m  = new double[2][nk2];
        C_k2 = new double[2][nk2];

        ck0_2 = new double[2];
    }

    public void setPosition(double xp1,double xp2,double x3){

        xp3 = x3;

        // b=true : below the point force. See formula in Hernandez-Ortiz et al

        double zb = h + xp3;  // target below source
        double za = h - xp3;  // target above source
        double ekz,emkz,shkz,chkz,zshkz,zchkz;

        double l,m,l2,m2,lm,k;

        // compute the c_{k,i} coefficients

        // q=0 terms
        ck0_1=za*zb;//(h*h-xp3*xp3);
        ck0_2[0]= zb;//(xp3+h);
        ck0_2[1]= -za;//(xp3-h);

        // q=/=0 terms
        for (int ij = 0; ij < nk2; ij++) {

            k  = K[ij];//sqrt(m2+l2);
            l  = lij[ij] ;
            l2 = l2ij[ij];
            m  = mij[ij];
            m2 = m2ij[ij];
            lm = lmij[ij];

            if(k!=0.0 ) {

                coskx[ij] = cos_apx(l * xp1  + m * xp2);
                sinkx[ij] = sin_apx(l * xp1  + m * xp2);

                // target below source
                ekz = exp_apx(k*zb);
                emkz = 1.0d/ekz;
                shkz = (ekz-emkz)/2;
                chkz = (ekz+emkz)/2;
                zshkz = zb*shkz;
                zchkz = zb*chkz / k;

                C_l2[0][ij] = (shkz + l2 * zchkz );
                C_lm[0][ij] = ( lm * zchkz );
                C_l [0][ij] = ( l * zshkz);
                C_m2[0][ij] = (shkz + m2 * zchkz );
                C_m [0][ij] = ( m * zshkz);
                C_k2[0][ij] = (shkz - (l2+m2) * zchkz);  //k2

                // target above source
                ekz = exp_apx(k*za);
                emkz = 1.0d/ekz;
                shkz = (ekz-emkz)/2;
                chkz = (ekz+emkz)/2;
                zshkz = za*shkz;
                zchkz = za*chkz / k;

                C_l2[1][ij] = (shkz + l2 * zchkz );
                C_lm[1][ij] = ( lm * zchkz );
                C_l [1][ij] = (- l * zshkz);
                C_m2[1][ij] = (shkz + m2 * zchkz );
                C_m [1][ij] = (- m * zshkz);
                C_k2[1][ij] = (shkz - (l2+m2) * zchkz);  //k2

            }

        }


    }

    public boolean getRelativePosition(double x03){
        return xp3<x03;
    }

    public double[] getCos(){
        return coskx;
    }
    public double[] getSin(){
        return sinkx;
    }

    public double[] getC_l2(boolean b){
        return C_l2[b?0:1];
    }
    public double[] getC_lm(boolean b){
        return C_lm[b?0:1];
    }
    public double[] getC_m2(boolean b){
        return C_m2[b?0:1];
    }
    public double[] getC_k2(boolean b){
        return C_k2[b?0:1];
    }
    public double[] getC_l(boolean b){
        return C_l[b?0:1];
    }
    public double[] getC_m(boolean b){
        return C_m[b?0:1];
    }

    public double getCk01(){
        return ck0_1;
    }
    public double getCk02(boolean b){
        return ck0_2[b?0:1];
    }

    public double[] getVelocity(double[][] lambda,double[] cF, boolean b){ // b=true <-> target below source

        double[] v = new double[3];

        double[] C_l2  = getC_l2(b);
        double[] C_m2  = getC_m2(b);
        double[] C_k2  = getC_k2(b);
        double[] C_l   = getC_l(b);
        double[] C_m   = getC_m(b);
        double[] C_lm  = getC_lm(b);

        double[] aF1_re = lambda[0];
        double[] aF1_im = lambda[3];

        double[] aF2_re = lambda[1];
        double[] aF2_im = lambda[4];

        double[] aF3_re = lambda[2];
        double[] aF3_im = lambda[5];

        //* computes velocity
        for (int ij = 0; ij < nk2; ij++) {// change the count l = 2pi/L*i

            // real part of v = Re1*Re2-Im1*Im2
            v[0] += coskx[ij] * ( C_l2[ij] * aF1_re[ij] + C_lm[ij] * aF2_re[ij] + C_l[ij] * aF3_im[ij]) //  Re1*Re2
                  + sinkx[ij] * (-C_l2[ij] * aF1_im[ij] - C_lm[ij] * aF2_im[ij] + C_l[ij] * aF3_re[ij]); // -Im1*Im2

            v[1] += coskx[ij] * ( C_lm[ij] * aF1_re[ij] + C_m2[ij] * aF2_re[ij] + C_m[ij] * aF3_im[ij]) //  Re*Re
                  + sinkx[ij] * (-C_lm[ij] * aF1_im[ij] - C_m2[ij] * aF2_im[ij] + C_m[ij] * aF3_re[ij]); // -Im*Im

            v[2] += coskx[ij] * (C_l[ij] * aF1_im[ij] + C_m[ij] * aF2_im[ij] + C_k2[ij] * aF3_re[ij]) //  Re*Re
                  + sinkx[ij] * (C_l[ij] * aF1_re[ij] + C_m[ij] * aF2_re[ij] - C_k2[ij] * aF3_im[ij]); // -Im*Im

        }
        //*/

        // q=0 terms
        v[0] += (cF[0]*ck0_1 + cF[1] * getCk02(b));
        v[1] += (cF[2]*ck0_1 + cF[3] * getCk02(b));

        return v;
    }


}
