/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package volume;

/**
 *
 * @author michel
 */
public class GradientVolume {

    public GradientVolume(Volume vol) {
        volume = vol;
        dimX = vol.getDimX();
        dimY = vol.getDimY();
        dimZ = vol.getDimZ();
        data = new VoxelGradient[dimX * dimY * dimZ];
        compute();
        maxmag = -1.0;
    }

    public VoxelGradient getGradient(int x, int y, int z) {
        return data[x + dimX * (y + dimY * z)];
    }

    public void setGradient(int x, int y, int z, VoxelGradient value) {
        data[x + dimX * (y + dimY * z)] = value;
    }

    public void setVoxel(int i, VoxelGradient value) {
        data[i] = value;
    }

    public VoxelGradient getVoxel(int i) {
        return data[i];
    }

    public int getDimX() {
        return dimX;
    }

    public int getDimY() {
        return dimY;
    }

    public int getDimZ() {
        return dimZ;
    }

    /**
     * Computes the gradient information of the volume according to Levoy's
     * paper.
     */
    private void compute() {
        // Compute the gradient for every voxel in the volume
        for (int x = 0; x < dimX; x++) {
            for (int y = 0; y < dimY; y++) {
                for (int z = 0; z < dimZ; z++) {
                    // The gradient on the edge of a volume is not defined, so if we're on the edge
                    // we just set the gradient to zero
                    if (x == 0 || y == 0 || z == 0 || x == dimX - 1 || y == dimY - 1
                            || z == dimZ - 1) {
                        // We are on the edge of the volume
                        setGradient(x, y, z, zero);
                    } else {
                        // We are not on the edge of the volume
                        double gx =
                                0.5 * (volume.getVoxel(x + 1, y, z) - volume.getVoxel(x - 1, y, z));
                        double gy =
                                0.5 * (volume.getVoxel(x, y + 1, z) - volume.getVoxel(x, y - 1, z));
                        double gz =
                                0.5 * (volume.getVoxel(x, y, z + 1) - volume.getVoxel(x, y, z - 1));

                        setGradient(x, y, z, new VoxelGradient((float) gx, (float) gy, (float) gz));
                    }
                }
            }
        }
    }

    public double getMaxGradientMagnitude() {
        if (maxmag >= 0) {
            return maxmag;
        } else {
            double magnitude = data[0].mag;
            for (int i = 0; i < data.length; i++) {
                magnitude = data[i].mag > magnitude ? data[i].mag : magnitude;
            }
            maxmag = magnitude;
            return magnitude;
        }
    }

    private int dimX, dimY, dimZ;
    private VoxelGradient zero = new VoxelGradient();
    VoxelGradient[] data;
    Volume volume;
    double maxmag;
}
