/*
 * #%L
 * Bio-Formats Plugins for ImageJ: a collection of ImageJ plugins including the
 * Bio-Formats Importer, Bio-Formats Exporter, Bio-Formats Macro Extensions,
 * Data Browser and Stack Slicer.
 * %%
 * Copyright (C) 2006 - 2013 Open Microscopy Environment:
 *   - Board of Regents of the University of Wisconsin-Madison
 *   - Glencoe Software, Inc.
 *   - University of Dundee
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 2 of the 
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public 
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-2.0.html>.
 * #L%
 */

package loci.plugins.util;

import ij.IJ;
import ij.ImagePlus;
import ij.gui.Line;
import ij.gui.MessageDialog;
import ij.gui.OvalRoi;
import ij.gui.PointRoi;
import ij.gui.PolygonRoi;
import ij.gui.Roi;
import ij.gui.ShapeRoi;
import ij.gui.TextRoi;
import ij.plugin.frame.RoiManager;

import java.awt.Color;
import java.awt.Frame;
import java.awt.Rectangle;
import java.util.ArrayList;
import java.util.List;

import loci.formats.MetadataTools;
import loci.formats.meta.IMetadata;
import loci.formats.meta.MetadataStore;
import loci.formats.ome.OMEXMLMetadata;
import ome.xml.model.Ellipse;
import ome.xml.model.Image;
import ome.xml.model.OME;
import ome.xml.model.Point;
import ome.xml.model.Polygon;
import ome.xml.model.Polyline;
import ome.xml.model.Shape;
import ome.xml.model.Union;

// TODO: Stored ROIs are not correctly linked to Image.

/**
 * Utility class for managing regions of interest within ImageJ.
 * Capable of constructing ROIs within ImageJ's ROI manager matching
 * those specified in an OME metadata store, and vice versa.
 *
 * <dl><dt><b>Source code:</b></dt>
 * <dd><a href="http://trac.openmicroscopy.org.uk/ome/browser/bioformats.git/components/bio-formats-plugins/src/loci/plugins/util/ROIHandler.java">Trac</a>,
 * <a href="http://git.openmicroscopy.org/?p=bioformats.git;a=blob;f=components/bio-formats-plugins/src/loci/plugins/util/ROIHandler.java;hb=HEAD">Gitweb</a></dd></dl>
 *
 * @author Melissa Linkert melissa at glencoesoftware.com
 */
public class ROIHandler {

    // -- ROIHandler API methods --

    /**
     * Look for ROIs in the given OMEXMLMetadata; if any are present, apply
     * them to the given images and display them in the ROI manager.
     */
    public static void openROIs(IMetadata retrieve, ImagePlus[] images) {
        if (!(retrieve instanceof OMEXMLMetadata)) return;
        int nextRoi = 0;
        RoiManager manager = RoiManager.getInstance();

        OME root = (OME) retrieve.getRoot();

        int imageCount = images.length;
        for (int imageNum=0; imageNum<imageCount; imageNum++) {
            int roiCount = root.sizeOfROIList();
            if (roiCount > 0 && manager == null) {
                manager = new RoiManager();
            }
            for (int roiNum=0; roiNum<roiCount; roiNum++) {
                Union shapeSet = root.getROI(roiNum).getUnion();
                int shapeCount = shapeSet.sizeOfShapeList();

                for (int shape=0; shape<shapeCount; shape++) {
                    Shape shapeObject = shapeSet.getShape(shape);

                    Roi roi = null;

                    if (shapeObject instanceof Ellipse) {
                        Ellipse ellipse = (Ellipse) shapeObject;
                        int cx = ellipse.getX().intValue();
                        int cy = ellipse.getY().intValue();
                        int rx = ellipse.getRadiusX().intValue();
                        int ry = ellipse.getRadiusY().intValue();
                        roi = new OvalRoi(cx - rx, cy - ry, rx * 2, ry * 2);
                    }
                    else if (shapeObject instanceof ome.xml.model.Line) {
                        ome.xml.model.Line line = (ome.xml.model.Line) shapeObject;
                        int x1 = line.getX1().intValue();
                        int x2 = line.getX2().intValue();
                        int y1 = line.getY1().intValue();
                        int y2 = line.getY2().intValue();
                        roi = new Line(x1, y1, x2, y2);
                    }
                    else if (shapeObject instanceof Point) {
                        Point point = (Point) shapeObject;
                        int x = point.getX().intValue();
                        int y = point.getY().intValue();
                        roi = new OvalRoi(x, y, 0, 0);
                    }
                    else if (shapeObject instanceof Polyline) {
                        Polyline polyline = (Polyline) shapeObject;
                        String points = polyline.getPoints();
                        int[][] coordinates = parsePoints(points);
                        roi = new PolygonRoi(coordinates[0], coordinates[1],
                                coordinates[0].length, Roi.POLYLINE);
                    }
                    else if (shapeObject instanceof Polygon) {
                        Polygon polygon = (Polygon) shapeObject;
                        String points = polygon.getPoints();
                        int[][] coordinates = parsePoints(points);
                        roi = new PolygonRoi(coordinates[0], coordinates[1],
                                coordinates[0].length, Roi.POLYGON);
                    }
                    else if (shapeObject instanceof ome.xml.model.Rectangle) {
                        ome.xml.model.Rectangle rectangle =
                                (ome.xml.model.Rectangle) shapeObject;
                        int x = rectangle.getX().intValue();
                        int y = rectangle.getY().intValue();
                        int w = rectangle.getWidth().intValue();
                        int h = rectangle.getHeight().intValue();
                        String label = shapeObject.getText();
                        if (label != null) {
                            roi = new TextRoi(x, y, label);
                        }
                        else {
                            roi = new Roi(x, y, w, h);
                        }
                    }
                    else if (shapeObject instanceof ome.xml.model.Label){
                        //add support for TextROI's
                    }

                    if (roi != null) {
                        Roi.setColor(Color.WHITE);
                        roi.setImage(images[imageNum]);
                        manager.add(images[imageNum], roi, nextRoi++);
                    }
                }
            }
        }
    }

    public static Roi[] readFromRoiManager(){

        RoiManager manager = RoiManager.getInstance();
        Roi[] rois = manager.getRoisAsArray();
        return rois;
    }

    /** Save ROIs in the ROI manager to the given MetadataStore. */
    public static void saveROIs(MetadataStore store) {
        Roi[] rois = readFromRoiManager();

        List<String> discardList = new ArrayList<String>();
        String roiID = null;int cntr = 0;
        for (int i=0; i<rois.length; i++) {

            String polylineID = MetadataTools.createLSID("Shape", cntr, 0);
            roiID = MetadataTools.createLSID("ROI", cntr, 0);

            if (rois[cntr].isDrawingTool()){//Checks if the given roi is a Text box/Arrow/Rounded Rectangle
                if (rois[cntr].getTypeAsString().matches("Text")){
                    store.setLabelID(polylineID, cntr, 0);
                    TextRoi c1 = (TextRoi) rois[cntr];

                    store.setLabelText(c1.getText(), cntr, 0);
                    store.setLabelX(c1.getPolygon().getBounds().getX(), cntr, 0);
                    store.setLabelY(c1.getPolygon().getBounds().getY(), cntr, 0);

                }
                else if (rois[cntr].getTypeAsString().matches("Rectangle")){
                    store.setRectangleID(polylineID, cntr, 0);
                    storeRectangle(rois[cntr], store, cntr, 0);
                }
                else {
                    roiID = null;
                    String type = rois[cntr].getName();
                    IJ.log("ROI ID : " + type + " ROI type : " +  "Arrow (Drawing Tool) is not supported");
                }
            }
            else if (rois[cntr] instanceof Line) {
                boolean checkpoint = rois[cntr].isDrawingTool();
                if (checkpoint != true){
                    store.setLineID(polylineID, cntr, 0);
                    storeLine((Line) rois[cntr], store, cntr, 0);
                }
                else {
                    roiID = null;
                    String type = rois[cntr].getName();
                    IJ.log("ROI ID : " + type + " ROI type : " +  "Arrow (Drawing Tool) is not supported");
                }
            }
            else if (rois[cntr] instanceof PolygonRoi) {
                if (rois[cntr].getTypeAsString().matches("Polyline") || rois[cntr].getTypeAsString().matches("Freeline")){
                    store.setPolylineID(polylineID, cntr, 0);
                    storePolygon((PolygonRoi) rois[cntr], store, cntr, 0);
                }
                else if (rois[cntr].getTypeAsString().matches("Point")){
                    store.setPointID(polylineID, cntr, 0);
                    storePoint((PointRoi) rois[cntr], store, cntr, 0);
                }
                else if (rois[cntr].getTypeAsString().matches("Polygon") || rois[cntr].getTypeAsString().matches("Angle") || rois[cntr].getTypeAsString().matches("Freehand") || rois[cntr].getTypeAsString().matches("Traced")){
                    store.setPolygonID(polylineID, cntr, 0);
                    storePolygon((PolygonRoi) rois[cntr], store, cntr, 0);
                }

            }

            else if (rois[cntr] instanceof ShapeRoi) {
                Roi[] subRois = ((ShapeRoi) rois[cntr]).getRois();
                for (int q=0; q<subRois.length; q++) {

                    polylineID = MetadataTools.createLSID("Shape", cntr, q);
                    roiID = MetadataTools.createLSID("ROI", cntr, q);

                    if (subRois[q] instanceof Line) {
                        boolean checkpoint = subRois[cntr].isDrawingTool();
                        if (checkpoint != true){
                            store.setLineID(polylineID, cntr, 0);
                            storeLine((Line) rois[cntr], store, cntr, 0);
                        }
                        else {
                            roiID = null;
                            String type1 = subRois[cntr].getName();
                            discardList.add(type1);
                            IJ.log("ROI ID : " + type1 + " ROI type : " + "Arrow (DrawingTool) is not supported");
                        }
                    }
                    else if (subRois[q] instanceof PolygonRoi) {
                        if (subRois[q].getTypeAsString().matches("Polyline") || subRois[q].getTypeAsString().matches("Freeline")){
                            store.setPolylineID(polylineID, cntr, q);
                            storePolygon((PolygonRoi) subRois[q], store, cntr, q);
                        }
                        else if (subRois[q].getTypeAsString().matches("Point")){
                            store.setPointID(polylineID, cntr, q);
                            storePoint((PointRoi) subRois[q], store, cntr, q);
                        }
                        else if (subRois[q].getTypeAsString().matches("Polygon") || subRois[q].getTypeAsString().matches("Angle") || subRois[q].getTypeAsString().matches("Freehand") || subRois[q].getTypeAsString().matches("Traced")){

                            store.setPolygonID(polylineID, cntr, q);
                            storePolygon((PolygonRoi) subRois[q], store, cntr, q);
                        }


                    }
                    else if (subRois[q] instanceof OvalRoi) {
                        store.setEllipseID(polylineID, cntr, q);
                        storeOval((OvalRoi) subRois[q], store, cntr, q);
                    }
                    else if (subRois[q] instanceof Roi){
                        store.setRectangleID(polylineID, cntr, q);
                        storeRectangle(subRois[q], store, cntr, q);
                    }
                    else {
                        roiID = null;
                        String type = subRois[cntr].getName();
                        IJ.log("ROI ID : " + type + " ROI type : " + subRois[cntr].getTypeAsString() + "is not supported");
                    }
                }
            }
            else if (rois[cntr] instanceof OvalRoi) {
                store.setEllipseID(polylineID, cntr, 0);
                storeOval((OvalRoi) rois[cntr], store, cntr, 0);
            }
            else if(rois[cntr] instanceof Roi){
                store.setRectangleID(polylineID, cntr, 0);
                storeRectangle(rois[cntr], store, cntr, 0);
            }
            else {

                roiID = null;
                String type = rois[cntr].getName();
                IJ.log("ROI ID : " + type + " ROI type : " + rois[cntr].getTypeAsString() + "is not supported");

            }

            //Save Roi's using ROIHandler
            if (roiID != null) {
                store.setROIID(roiID, cntr);
                store.setImageROIRef(roiID, 0, cntr);
                cntr++;
            }
        }
    }

    // -- Helper methods --

    private static void storePoint(PointRoi roi, MetadataStore store,
            int roiNum, int shape) {


        int[] xCoordinates = roi.getPolygon().xpoints;;
        int[] yCoordinates = roi.getPolygon().ypoints;;

        for (int cntr=0 ; cntr<xCoordinates.length; cntr++){
            String polylineID = MetadataTools.createLSID("Shape", roiNum, shape+cntr);
            store.setPointID(polylineID, roiNum, shape+cntr);
            store.setPointX((double) xCoordinates[cntr], roiNum, shape+cntr);
            store.setPointY((double) yCoordinates[cntr], roiNum, shape+cntr);
        }
    }

    /** Store a Line ROI in the given MetadataStore. */
    private static void storeLine(Line roi, MetadataStore store,
            int roiNum, int shape)
    {
        store.setLineX1(new Double(roi.x1), roiNum, shape);
        store.setLineX2(new Double(roi.x2), roiNum, shape);
        store.setLineY1(new Double(roi.y1), roiNum, shape);
        store.setLineY2(new Double(roi.y2), roiNum, shape);
    }

    /** Store an Roi (rectangle) in the given MetadataStore. */
    private static void storeRectangle(Roi roi, MetadataStore store,
            int roiNum, int shape)
    {
        Rectangle bounds = roi.getBounds();
        store.setRectangleX(new Double(bounds.x), roiNum, shape);
        store.setRectangleY(new Double(bounds.y), roiNum, shape);
        store.setRectangleWidth(new Double(bounds.width), roiNum, shape);
        store.setRectangleHeight(new Double(bounds.height), roiNum, shape);
    }

    /** Store a Polygon ROI in the given MetadataStore. */
    private static void storePolygon(PolygonRoi roi, MetadataStore store,
            int roiNum, int shape)
    {
        Rectangle bounds = roi.getBounds();
        int[] xCoordinates = roi.getXCoordinates();
        int[] yCoordinates = roi.getYCoordinates();
        StringBuffer points = new StringBuffer();
        for (int cntr=0; cntr<xCoordinates.length; cntr++) {
            points.append(xCoordinates[cntr] + bounds.x);
            points.append(",");
            points.append(yCoordinates[cntr] + bounds.y);
            if (cntr < xCoordinates.length - 1) points.append(" ");
        }
        String st1 = roi.getTypeAsString();
        if (st1.matches("Polyline") || st1.matches("Freeline")) {
            store.setPolylinePoints(points.toString(), roiNum, shape);
        }
        else if (st1.matches("Polygon") || st1.matches("Angle") || st1.matches("Freehand") || st1.matches("Traced")){
            store.setPolygonPoints(points.toString(), roiNum, shape);
        }
        else{
            store.setPolygonPoints(points.toString(), roiNum, shape);
        }

    }

    /** Store an Oval ROI in the given MetadataStore. */
    @SuppressWarnings("unused")
    private static void storeOval(OvalRoi roi,
            MetadataStore store, int roiNum, int shape)
    {
        Rectangle vnRectBounds = roi.getPolygon().getBounds();
        int x = vnRectBounds.x;
        int y = vnRectBounds.y;

        double rx = vnRectBounds.getWidth();
        double ry = vnRectBounds.getHeight();

        store.setEllipseX(((double) x + rx/2), roiNum, shape);
        store.setEllipseY(((double) y + ry/2), roiNum, shape);
        store.setEllipseRadiusX((double) rx/2, roiNum, shape);
        store.setEllipseRadiusY((double) ry/2, roiNum, shape);
        // TODO: storeOval
        // TODO: storeOval
    }

    /**
     * Parse (x, y) coordinates from a String returned by
     * MetadataRetrieve.getPolygonpoints(...) or
     * MetadataRetrieve.getPolylinepoints(...)
     */
    private static int[][] parsePoints(String points) {
        // assuming points are stored like this:
        // x0,y0 x1,y1 x2,y2 ...
        String[] pointList = points.split(" ");
        int[][] coordinates = new int[2][pointList.length];

        for (int q=0; q<pointList.length; q++) {
            pointList[q] = pointList[q].trim();
            int delim = pointList[q].indexOf(",");
            coordinates[0][q] =
                    (int) Double.parseDouble(pointList[q].substring(0, delim));
            coordinates[1][q] =
                    (int) Double.parseDouble(pointList[q].substring(delim + 1));
        }
        return coordinates;
    }

}
