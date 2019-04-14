package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.text.NumberFormat;
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Hashtable;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TimeZone;
import java.util.Vector;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import java.util.stream.Collectors;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.ITableColorProvider;
import org.eclipse.jface.viewers.ITableFontProvider;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.PaintEvent;
import org.eclipse.swt.events.PaintListener;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Rectangle;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IHyperlinkListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Hyperlink;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.progress.UIJob;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAFastPartitioner;
import org.lamport.tla.toolbox.editor.basic.TLAPartitionScanner;
import org.lamport.tla.toolbox.editor.basic.TLASourceViewerConfiguration;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformation;
import org.lamport.tla.toolbox.tool.tlc.output.data.CoverageInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.StateSpaceInformationItem;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.TLACoverageEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ActionClickListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.FontPreferenceChangeListener;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A page to display results of model checking (the "third tab"
 * of the model editor).
 * @author Simon Zambrovski
 */
public class ResultPage extends BasicFormPage implements ITLCModelLaunchDataPresenter
{
	
	public static final String RESULT_PAGE_PROBLEM = "ResultPageProblem";

    public static final String ID = "resultPage";

    private static final String TOOLTIP = "Click on a row to go to action.";

    private Hyperlink errorStatusHyperLink;
    /**
     * UI elements
     */
    private SourceViewer userOutput;
    private SourceViewer progressOutput;
    private SourceViewer expressionEvalResult;
    private SourceViewer expressionEvalInput;
    private long startTimestamp;
    private Text startTimestampText;
    // startTime is provided by the TLCModelLaunchDataProvider's getStartTime()
    // method.
    private Text finishTimestampText;
    private Text tlcModeText;
    private Text lastCheckpointTimeText;
    private Text coverageTimestampText;
    private Text currentStatusText;
    private Text fingerprintCollisionProbabilityText;
    private TableViewer coverage;
    private TableViewer stateSpace;
	private final Map<String, Section> sections = new HashMap<String, Section>();
    private final Lock disposeLock = new ReentrantLock(true);

    // listener on changes to the tlc output font preference
    private FontPreferenceChangeListener fontChangeListener;

    // hyper link listener activated in case of errors
    protected IHyperlinkListener errorHyperLinkListener = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            if (getModel() != null)
            {
            	getModel().setOriginalTraceShown(true);
                TLCErrorView.updateErrorView(getModel());
            }
        }
    };

	private IMarker incompleteStateExploration;
	private IMarker zeroCoverage;

    /**
     * Constructor for the page
     * @param editor
     */
    public ResultPage(FormEditor editor)
    {
        super(editor, ID, "Model Checking Results",
        		"icons/full/results_page_" + IMAGE_TEMPLATE_TOKEN + ".png");
        this.helpId = IHelpConstants.RESULT_MODEL_PAGE;
    }

    /**
     * Will be called by the provider on data changes
     */
    public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId)
    {
        UIHelper.runUIAsync(new Runnable() {
			public void run() {
				// Acquire dispose lock prior to widget access. Using a single
				// lock just to serialize dispose and modelChange seems
				// overkill, but the wait-for graph becomes tricky with all the
				// background jobs going on (at least too tricky to get it
				// solved within an hour).
            	disposeLock.lock();
            	try {
                	if (getPartControl().isDisposed()) {
            			// Don't update the widgets if the underlying SWT control has
            			// already been disposed. Otherwise it results in an
            			// "SWTException: Widget is disposed".
                		return;
                	}
					switch (fieldId) {
	                case USER_OUTPUT:
	                    ResultPage.this.userOutput.setDocument(dataProvider.getUserOutput());
	                    break;
	                case PROGRESS_OUTPUT:
	                    ResultPage.this.progressOutput.setDocument(dataProvider.getProgressOutput());
	                    break;
	                case CONST_EXPR_EVAL_OUTPUT:
	                    ResultPage.this.expressionEvalResult.getTextWidget().setText(dataProvider.getCalcOutput());
	                    break;
	                case START_TIME:
	                    ResultPage.this.startTimestamp = dataProvider.getStartTimestamp();
	                    if (ResultPage.this.startTimestamp < 0) {
							// Leave the starttime text empty on a negative
							// timestamp. A negative one indicates that the
							// model has never been checked. See Long.MIN_VALUE in
	                    	// org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider.initialize()
	                    	ResultPage.this.startTimestampText.setText("");
	                    	break;
	                    }
						ResultPage.this.startTimestampText.setText(new Date(ResultPage.this.startTimestamp).toString());
	                    break;
	                case END_TIME:
	                    long finishTimestamp = dataProvider.getFinishTimestamp();
	                    if(finishTimestamp < 0) {
	                    	ResultPage.this.finishTimestampText.setText("");
	                    	break;
	                    }
	                    ResultPage.this.finishTimestampText.setText(new Date(finishTimestamp).toString());
	                    
	                    // calc elapsed time and set as Tooltip
	                    final SimpleDateFormat sdf = new SimpleDateFormat("HH:mm:ss");
	                    sdf.setTimeZone(TimeZone.getTimeZone("GMT")); // explicitly set TZ to handle local offset
	                    long elapsedTime = finishTimestamp - dataProvider.getStartTimestamp();
	                    ResultPage.this.finishTimestampText.setToolTipText(sdf.format(new Date(elapsedTime)));
	                    ResultPage.this.startTimestampText.setToolTipText(sdf.format(new Date(elapsedTime)));
	                    break;
	                case TLC_MODE:
	                	ResultPage.this.tlcModeText.setText(dataProvider.getTLCMode());
	                	((AdvancedModelPage) getEditor().findPage(AdvancedModelPage.ID)).setFpIndex(dataProvider.getFPIndex());
	                case LAST_CHECKPOINT_TIME:
	                    long lastCheckpointTimeStamp = dataProvider.getLastCheckpointTimeStamp();
	                    if(lastCheckpointTimeStamp > 0) {
	                    	ResultPage.this.lastCheckpointTimeText.setText(new Date(lastCheckpointTimeStamp).toString());
	                    	break;
	                    }
	                   	ResultPage.this.lastCheckpointTimeText.setText("");
	                   	break;
	                case CURRENT_STATUS:
	                    ResultPage.this.currentStatusText.setText(dataProvider.getCurrentStatus());
	                    break;
	                case FINGERPRINT_COLLISION_PROBABILITY:
	                    ResultPage.this.fingerprintCollisionProbabilityText.setText(dataProvider.getFingerprintCollisionProbability());
	                    break;
	                case COVERAGE_TIME:
	                    ResultPage.this.coverageTimestampText.setText(dataProvider.getCoverageTimestamp());
	                    break;
	                case COVERAGE:
	                	final CoverageInformation coverageInfo = dataProvider.getCoverageInfo();
	                	ResultPage.this.coverage.setInput(coverageInfo);
						if (dataProvider.isDone() && !coverageInfo.isEmpty()) {
							if (dataProvider.hasZeroCoverage()) {
								if (zeroCoverage == null) {
									final Hashtable<String, Object> marker = ModelHelper.createMarkerDescription(
											"Coverage is zero for one or more modules.", IMarker.SEVERITY_WARNING);
									marker.put(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_PAGE, 2);
									zeroCoverage = getModel().setMarker(marker, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
								}
							} else if (zeroCoverage != null) {
								try {
									zeroCoverage.delete();
									ResultPage.this.resetMessage(RESULT_PAGE_PROBLEM);
									zeroCoverage = null;
								} catch (CoreException e) {
									TLCUIActivator.getDefault().logError(e.getMessage(), e);
								}
							}
						}
	                    break;
	                case COVERAGE_END:
	                	final CoverageInformation ci = dataProvider.getCoverageInfo();
	                	if (ci.isEmpty() || ci.isLegacy()) {
							// Cannot show coverage information without (non-legacy) coverage data.
	                		break;
	                	}
						final ModelEditor modelEditor = (ModelEditor) ResultPage.this.getEditor();
						
						final List<IFile> savedTLAFiles = modelEditor.getModel().getSavedTLAFiles();
						for (IFile iFile : savedTLAFiles) {
							if (!ci.has(iFile)) {
								continue;
							}
							// Open the files as pages of the current model editor.
							final FileEditorInput input = new FileEditorInput(iFile);
							final IEditorPart[] findEditors = modelEditor.findEditors(input);
							try {
								if (findEditors.length == 0) {
									modelEditor.addPage(new TLACoverageEditor(ci.projectionFor(iFile)), input);
								} else {
									if (findEditors[0] instanceof TLACoverageEditor) {
										final TLACoverageEditor coverageEditor = (TLACoverageEditor) findEditors[0];
										coverageEditor.resetInput(ci.projectionFor(iFile));
									}
								}
							} catch (PartInitException e) {
								TLCUIActivator.getDefault().logError(e.getMessage(), e);
							}
						}
	                	break;
	                case PROGRESS:
	                    ResultPage.this.stateSpace.setInput(dataProvider.getProgressInformation());
	
	                    // The following code finds all the graph windows (shells) for this
	                    // model and calls redraw() and update() on them, which apparently is the
	                    // magic incantation to cause its listener to be called to issue the
	                    // necessary commands to redraw the data and then displays the result.
	                    String suffix = getGraphTitleSuffix(ResultPage.this);
	                    Shell[] shells = UIHelper.getCurrentDisplay().getShells();
	                    for (int i = 0; i < shells.length; i++)
	                    {
	                        if (shells[i].getText().endsWith(suffix))
	                        {
	                            shells[i].redraw();
	                            shells[i].update();
	                            // The following was commented out by LL on 6 Jul 2012 because it was filling
	                            // up the Console log with useless stuff.
	                            // TLCUIActivator.getDefault().logDebug("Called redraw/update on shell number" + i);
	                        }
	                    }
	                    break;
	                case WARNINGS:
						if (dataProvider.isSymmetryWithLiveness()) {
							final MainModelPage mmp = (MainModelPage) getModelEditor().getFormPage(MainModelPage.ID);
							final Optional<Assignment> possibleSymmetrySet = mmp.getConstants().stream()
									.filter(c -> c.isSymmetricalSet()).findFirst();
							if (possibleSymmetrySet.isPresent()) {
								final Assignment symmetrySet = possibleSymmetrySet.get();
								getModelEditor().addErrorMessage(new ErrorMessage(String.format("%s %s",
										symmetrySet.getLabel(),
										"declared to be symmetric. Liveness checking under symmetry might fail to find a violation."),
										symmetrySet.getLabel(), MainModelPage.ID,
										Arrays.asList(ISectionConstants.SEC_WHAT_IS_THE_MODEL,
												ISectionConstants.SEC_WHAT_TO_CHECK_PROPERTIES),
										IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS));
							}
						}
						break;
	                case ERRORS:
	                    String text;
	                    Color color;
	                    int errorCount = dataProvider.getErrors().size();
	                    switch (errorCount) {
	                    case 0:
	                        text = TLCModelLaunchDataProvider.NO_ERRORS;
	                        color = TLCUIActivator.getColor(SWT.COLOR_BLACK);
	                        ResultPage.this.errorStatusHyperLink
	                                .removeHyperlinkListener(ResultPage.this.errorHyperLinkListener);
	                        break;
	                    case 1:
	                        text = "1 Error";
	                        ResultPage.this.errorStatusHyperLink
	                                .addHyperlinkListener(ResultPage.this.errorHyperLinkListener);
	                        color = TLCUIActivator.getColor(SWT.COLOR_RED);
	                        break;
	                    default:
	                        text = String.valueOf(errorCount) + " Errors";
	                        ResultPage.this.errorStatusHyperLink
	                                .addHyperlinkListener(ResultPage.this.errorHyperLinkListener);
	                        color = TLCUIActivator.getColor(SWT.COLOR_RED);
	                        break;
	                    }
	
	                    ResultPage.this.errorStatusHyperLink.setText(text);
	                    ResultPage.this.errorStatusHyperLink.setForeground(color);
						
	                    // update the error view
	                    TLCErrorView.updateErrorView(dataProvider.getModel());
	                    break;
	                default:
	                    break;
	                }
					
					// Set label provider to highlight unexplored states if
					// TLC is done but not all states are explored.
					if (ResultPage.this.stateSpace.getLabelProvider() instanceof StateSpaceLabelProvider) {
						final StateSpaceLabelProvider sslp = (StateSpaceLabelProvider) ResultPage.this.stateSpace
								.getLabelProvider();
						if (dataProvider.isDone() && dataProvider.getProgressInformation().size() > 0) {
							final long statesLeft = dataProvider.getProgressInformation().get(0).getLeftStates();
							if (statesLeft > 0) {
								sslp.setHighlightUnexplored();
								// Create a problem marker which gets displayed by
								// BasicFormPage/ModelEditor as a warning on the
								// result page.
								if (incompleteStateExploration == null) {
									final Hashtable<String, Object> marker = ModelHelper.createMarkerDescription(
											"State space exploration incomplete", IMarker.SEVERITY_WARNING);
									marker.put(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_PAGE, 2);
									incompleteStateExploration = getModel().setMarker(marker, ModelHelper.TLC_MODEL_ERROR_MARKER_TLC);
								}
							} else {
								if (incompleteStateExploration != null) {
									try {
										incompleteStateExploration.delete();
										ResultPage.this.resetMessage(RESULT_PAGE_PROBLEM);
										incompleteStateExploration = null;
									} catch (CoreException e) {
										TLCUIActivator.getDefault().logError(e.getMessage(), e);
									}
								}
								sslp.unsetHighlightUnexplored();
							}
						}
						ResultPage.this.stateSpace.refresh();
					}
					

            	} finally {
            		disposeLock.unlock();
            	}
            }
        });

    }

    /**
     * Gets the data provider for the current page
     */
    public void loadData() throws CoreException
    {

		TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
		TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(getModel());
		if (provider != null) {
			provider.setPresenter(this);
		} else {
			// no data provider
			reinit();
		}

		// constant expression
		final Document document = new Document(getModel().getEvalExpression());
		final IDocumentPartitioner partitioner = new TLAFastPartitioner(
				TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
		document.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
		partitioner.connect(document);
		expressionEvalInput.setDocument(document);
	}

    /**
     * Reinitialize the fields
     * has to be run in the UI thread
     */
    private synchronized void reinit()
    {
        // TLCUIActivator.getDefault().logDebug("Entering reinit()");
    	disposeLock.lock();
    	try {
    		if (getPartControl().isDisposed()) {
    			// Cannot access widgets past their disposal
    			return;
    		}
    		this.startTimestampText.setText("");
    		this.startTimestamp = 0;
    		this.finishTimestampText.setText("");
    		this.tlcModeText.setText("");
    		this.lastCheckpointTimeText.setText("");
    		this.currentStatusText.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
    		this.errorStatusHyperLink.setText(TLCModelLaunchDataProvider.NO_ERRORS);
    		this.coverage.setInput(new Vector<CoverageInformationItem>());
    		this.stateSpace.setInput(new Vector<StateSpaceInformationItem>());
    		this.progressOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
    		this.userOutput.setDocument(new Document(TLCModelLaunchDataProvider.NO_OUTPUT_AVAILABLE));
    	} finally {
    		disposeLock.unlock();
    	}
        // TLCUIActivator.getDefault().logDebug("Exiting reinit()");
    }

    /**
     * Dispose the page
     */
    public void dispose()
    {
    	disposeLock.lock();
		try {
			/*
			 * Remove graph windows raised for the page.
			 */
			String suffix = getGraphTitleSuffix(this);
			Shell[] shells = UIHelper.getCurrentDisplay().getShells();
			for (int i = 0; i < shells.length; i++) {
				if (shells[i].getText().endsWith(suffix)) {
					shells[i].dispose();
				}
			}

			if (incompleteStateExploration != null) {
				incompleteStateExploration.delete();
				incompleteStateExploration = null;
			}
			
			if (zeroCoverage != null) {
				zeroCoverage.delete();
				zeroCoverage = null;
			}

			JFaceResources.getFontRegistry().removeListener(fontChangeListener);

			TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry()
					.getProvider(getModel());
			if (provider != null) {
				provider.setPresenter(null);
			}
			super.dispose();
		} catch (CoreException e) {
			e.printStackTrace();
		} finally {
			disposeLock.unlock();
		}
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
	protected Layout getBodyLayout() {
		return FormHelper.createFormTableWrapLayout(true, 1);
	}

    /**
     * Draw the fields
     * 
     * Its helpful to know what the standard SWT widgets look like.
     * Pictures can be found at http://www.eclipse.org/swt/widgets/
     * 
     * Layouts are used throughout this method.
     * A good explanation of layouts is given in the article
     * http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        final int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED | SWT.WRAP;
        final int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.READ_ONLY | SWT.FULL_SELECTION | SWT.WRAP;

        final FormToolkit toolkit = managedForm.getToolkit();
        final Composite body = managedForm.getForm().getBody();

        TableWrapData twd;
        Section section;
        GridLayout gl;
        GridData gd;

        TableWrapLayout twl = new TableWrapLayout();
        twl.leftMargin = 0;
        twl.rightMargin = 0;
        body.setLayout(twl);

        // -------------------------------------------------------------------
        // general section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSectionComposite(body, "General", ""
        /* "The current progress of model-checking"*/, toolkit, sectionFlags & ~Section.DESCRIPTION,
                getExpansionListener());
        sections.put(SEC_GENERAL, section);
        twd = new TableWrapData();
        twd.grabHorizontal = true;
        twd.align = TableWrapData.FILL;
        section.setLayoutData(twd);

        final Composite generalArea = (Composite) section.getClient();
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        generalArea.setLayout(gl);

        // start
        this.startTimestampText = FormHelper.createTextLeft("Start time:", generalArea, toolkit);
        this.startTimestampText.setEditable(false);
        // elapsed time
        this.finishTimestampText = FormHelper.createTextLeft("End time:", generalArea, toolkit);
        this.finishTimestampText.setEditable(false);
        // elapsed time
        this.tlcModeText = FormHelper.createTextLeft("TLC mode:", generalArea, toolkit);
        this.tlcModeText.setEditable(false);
       // last checkpoint time
        this.lastCheckpointTimeText = FormHelper.createTextLeft("Last checkpoint time:", generalArea, toolkit);
        this.lastCheckpointTimeText.setEditable(false);
        // current status
        this.currentStatusText = FormHelper.createTextLeft("Current status:", generalArea, toolkit);
        this.currentStatusText.setEditable(false);
        this.currentStatusText.setText(TLCModelLaunchDataProvider.NOT_RUNNING);
        // errors
        // Label createLabel =
        // toolkit.createLabel(statusComposite, "Errors detected:");
        // this.errorStatusHyperLink = toolkit.createHyperlink(statusComposite, "", SWT.RIGHT);
        this.errorStatusHyperLink = FormHelper.createHyperlinkLeft("Errors detected:", generalArea, toolkit);
        // fingerprint collision probability
        this.fingerprintCollisionProbabilityText = FormHelper.createTextLeft("Fingerprint collision probability:", generalArea, toolkit);
        this.fingerprintCollisionProbabilityText.setEditable(false);
        this.fingerprintCollisionProbabilityText.setText("");

        
        // -------------------------------------------------------------------
        // statistics section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSectionComposite(body, "Statistics", "", toolkit,
        		(sectionFlags | Section.COMPACT) & ~Section.DESCRIPTION, getExpansionListener());
        sections.put(SEC_STATISTICS, section);
        twd = new TableWrapData();
        twd.grabHorizontal = true;
        twd.align = TableWrapData.FILL;
        section.setLayoutData(twd);
        
        final Composite statArea = (Composite) section.getClient();
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        statArea.setLayout(gl);

        // progress stats
        createAndSetupStateSpace(statArea, toolkit);
        
        // coverage stats
        createAndSetupCoverage(statArea, toolkit);

        
        // -------------------------------------------------------------------
        // Calculator section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
		section = FormHelper.createSectionComposite(body, "Evaluate Constant Expression", "",
				toolkit, sectionFlags & ~Section.DESCRIPTION, getExpansionListener());
        sections.put(SEC_EXPRESSION, section);

        Composite resultArea = (Composite) section.getClient();
        GridLayout gLayout = new GridLayout(2, false);
        gLayout.marginHeight = 0;
        resultArea.setLayout(gLayout);

        final Composite expressionComposite = toolkit.createComposite(resultArea);
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        gd.minimumWidth = 360;
        expressionComposite.setLayoutData(gd);
        twl = new TableWrapLayout();
        twl.numColumns = 1;
        twl.topMargin = 0;
        twl.bottomMargin = 5;
        expressionComposite.setLayout(twl);

        Label l = toolkit.createLabel(expressionComposite, "Expression: ");
		twd = new TableWrapData();
		twd.maxWidth = 360;
		l.setLayoutData(twd);
		expressionEvalInput = FormHelper.createFormsSourceViewer(toolkit, expressionComposite, textFieldFlags,
				new TLASourceViewerConfiguration());
		expressionEvalInput.getTextWidget().addKeyListener(new KeyListener() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (isUndoKeyPress(e)) {
					expressionEvalInput.doOperation(ITextOperationTarget.UNDO);
				} else if (isRedoKeyPress(e)) {
					expressionEvalInput.doOperation(ITextOperationTarget.REDO);
				}
			}

			private boolean isRedoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'y') || (e.keyCode == 'Y'));
			}

			private boolean isUndoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'z') || (e.keyCode =='Z'));
			}

			@Override
			public void keyReleased(KeyEvent e) { }
		});
        
        // Reminder that this grid data is for this text area within the expression composite within the result area
		twd = new TableWrapData();
		twd.align = TableWrapData.FILL;
		twd.grabHorizontal = true;
		twd.maxWidth = 360;
		twd.heightHint = 80;
		twd.valign = TableWrapData.MIDDLE;
        expressionEvalInput.getTextWidget().setLayoutData(twd);
		
        // We want the value section to get larger as the window
        // gets larger but not the expression section.
		final Composite valueComposite = toolkit.createComposite(resultArea);
        gd = new GridData(SWT.FILL, SWT.FILL, true, false);
        gd.minimumWidth = 360;
        valueComposite.setLayoutData(gd);
        twl = new TableWrapLayout();
        twl.numColumns = 1;
        twl.topMargin = 0;
        twl.bottomMargin = 5;
        valueComposite.setLayout(twl);

        l = toolkit.createLabel(valueComposite, "Value: ");
		twd = new TableWrapData();
		twd.maxWidth = 360;
		l.setLayoutData(twd);
        expressionEvalResult = FormHelper.createFormsOutputViewer(toolkit, valueComposite, textFieldFlags);

        // Reminder that this grid data is for this text area within the value composite within the result area
		twd = new TableWrapData();
		twd.align = TableWrapData.FILL;
		twd.grabHorizontal = true;
		twd.maxWidth = 360;
		twd.heightHint = 80;
		twd.valign = TableWrapData.MIDDLE;
		expressionEvalResult.getTextWidget().setLayoutData(twd);

        // We want this font to be the same as the input.
        // If it was not set it would be the same as the font
        // in the module editor.
        expressionEvalResult.getTextWidget().setFont(JFaceResources.getTextFont());
        expressionEvalInput.getTextWidget().setFont(JFaceResources.getTextFont());
        // This is required to paint the borders of the text boxes
        // it must be called on the direct parent of the widget
        // with a border. There is a call of this method in
        // FormHelper.createSectionComposite, but that is called
        // on the section which is not a direct parent of the
        // text box widget.
        toolkit.paintBordersFor(expressionComposite);
        toolkit.paintBordersFor(valueComposite);

        ValidateableSectionPart calculatorSectionPart = new ValidateableSectionPart(section, this, SEC_EXPRESSION);
        // This ensures that when the part is made dirty, the model
        // appears unsaved.
        managedForm.addPart(calculatorSectionPart);

        // This makes the widget unsaved when text is entered.
        expressionEvalInput.getTextWidget().addModifyListener(new DirtyMarkingListener(calculatorSectionPart, false));

        getDataBindingManager().bindAttribute(Model.MODEL_EXPRESSION_EVAL, expressionEvalInput, calculatorSectionPart);
        getDataBindingManager().bindSection(calculatorSectionPart, SEC_EXPRESSION, getId());

                
        // -------------------------------------------------------------------
        // output section
        section = FormHelper.createSectionComposite(body, "User Output",
                "TLC output generated by evaluating Print and PrintT expressions.", toolkit, sectionFlags,
                getExpansionListener());
        sections.put(SEC_OUTPUT, section);
        final Composite outputArea = (Composite) section.getClient();
        twl = new TableWrapLayout();
        twl.numColumns = 1;
        outputArea.setLayout(twl);
        // output viewer -- see progressOutput comment complaints concerning SWT.WRAP included in the text field flags
        userOutput = FormHelper.createFormsOutputViewer(toolkit, outputArea, textFieldFlags);
        twd = new TableWrapData();
        twd.maxWidth = 600;
        twd.maxHeight = 240;
        twd.grabHorizontal = true;
        userOutput.getTextWidget().setLayoutData(twd);
        userOutput.getTextWidget().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        // -------------------------------------------------------------------
        // progress section
        // There is no description line for this section, so it is
        // necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an
        // extra empty line would appear below the title.
        section = FormHelper.createSectionComposite(body, "Progress Output", "  ", toolkit,
				(sectionFlags & ~Section.EXPANDED), getExpansionListener());
        sections.put(SEC_PROGRESS, section);
        Composite progressArea = (Composite) section.getClient();
        progressArea = (Composite) section.getClient();
        twl = new TableWrapLayout();
        twl.numColumns = 1;
        progressArea.setLayout(twl);

        // I am regularly stunned by how crappy and quirky SWT is... in this case, if we don't have SWT.WRAP in the,
        //		flags mask, the below maxWidth is observed on expansion of the text area (which we really don't want)
        //		but if we turn on WRAP, then the text area expands to fill the entire width but observes width shrinking
        //		of its parent editor. If we instead use GridLayout (with or without WRAP), width shrinking is 
        //		completely ignored and the width of the text area is the longest line of text...
        progressOutput = FormHelper.createFormsOutputViewer(toolkit, progressArea, textFieldFlags);
        twd = new TableWrapData();
        twd.maxWidth = 600;
        twd.maxHeight = 240;
        twd.grabHorizontal = true;
        progressOutput.getTextWidget().setLayoutData(twd);
        progressOutput.getTextWidget().setFont(JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_OUTPUT_FONT));

        Vector<Control> controls = new Vector<Control>();
        controls.add(userOutput.getControl());
        controls.add(progressOutput.getControl());
        fontChangeListener = new FontPreferenceChangeListener(controls, ITLCPreferenceConstants.I_TLC_OUTPUT_FONT);

        JFaceResources.getFontRegistry().addListener(fontChangeListener);
        
        headClientTBM.add(new DynamicContributionItem(new LoadOutputAction()));
    }

	class LoadOutputAction extends Action {
		public LoadOutputAction() {
			super("Load output", TLCUIActivator.imageDescriptorFromPlugin(
					TLCUIActivator.PLUGIN_ID,
					"icons/full/copy_edit.gif"));
			setDescription("Loads the output from an external model run (requires \"-tool\" parameter) corresponding to this model.");
			setToolTipText(
					"Loads an existing output (e.g. from a standlone TLC run that corresponds to this model). Output has to contain tool markers. Run TLC with \"-tool\" command line parameter.	");
		}

		public void run() {
			// Get the user input (the path to the TLC output file).
			final FileDialog fileDialog = new FileDialog(new Shell());
			final String path = fileDialog.open();
			if (path == null) {
				// User cancelled the dialog
				return;
			}
			
			// I/O operations should never run inside the UI thread.
			final Job j = new WorkspaceJob("Loading output file...") {
				public IStatus runInWorkspace(final IProgressMonitor monitor) throws CoreException {
					try {
						// Import the file into the Toolbox on the file/resource layer.
						final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry
								.getModelCheckSourceRegistry();
						modelCheckSourceRegistry
								.removeTLCStatusSource(new Model[] { getModel() });
						getModel().createModelOutputLogFile(new FileInputStream(new File(path)), monitor);
						
						// Once the output has been imported on the
						// file/resource layer, update the UI.
						final Job job = new UIJob("Updating results page with loaded output...") {
							public IStatus runInUIThread(IProgressMonitor monitor) {
								try {
									ResultPage.this.loadData();
								} catch (CoreException e) {
									return new Status(IStatus.ERROR, TLCUIActivator.PLUGIN_ID, e.getMessage(), e);
								}
								return Status.OK_STATUS;
							}
						};
						job.schedule();
						
					} catch (FileNotFoundException e) {
						return new Status(IStatus.ERROR, TLCUIActivator.PLUGIN_ID, e.getMessage(), e);
					}
	                return Status.OK_STATUS;
				}
			};
		   	final IWorkspace workspace = ResourcesPlugin.getWorkspace();
			j.setRule(workspace.getRuleFactory().buildRule());
			j.schedule();
		}

		/* (non-Javadoc)
		 * @see org.eclipse.jface.action.Action#isEnabled()
		 */
		public boolean isEnabled() {
			if (getModel().isRunning()) {
				return false;
			}
			return super.isEnabled();
		}
	}


    /**
     * Save data back to model
     */
    public void commit(boolean onSave)
    {
        String expression = this.expressionEvalInput.getDocument().get();
        getModel().unsavedSetEvalExpression(expression);

        super.commit(onSave);
    }

    /**
     * Creates the state space table (initializes the {@link stateSpace} variable)
     * @param parent
     * @param toolkit
     * @return the constructed composite
     */
    private Composite createAndSetupStateSpace(final Composite parent, final FormToolkit toolkit) {
        final Composite statespaceComposite = toolkit.createComposite(parent, SWT.WRAP);
        GridLayout gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        statespaceComposite.setLayout(gl);
        GridData gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        statespaceComposite.setLayoutData(gd);

        final Label title
        	= toolkit.createLabel(statespaceComposite, "State space progress (click column header for graph)");
        gd = new GridData();
        gd.heightHint = 22;
        gd.horizontalAlignment = SWT.BEGINNING;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 6;
        title.setLayoutData(gd);
        
		final Table stateTable
			= toolkit.createTable(statespaceComposite, (SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL | SWT.BORDER));
        gd = new GridData();
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = StateSpaceLabelProvider.MIN_WIDTH;
        gd.heightHint = 100;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalAlignment = SWT.FILL;
        stateTable.setLayoutData(gd);

        stateTable.setHeaderVisible(true);
        stateTable.setLinesVisible(true);

        StateSpaceLabelProvider.createTableColumns(stateTable, this);

        // create the viewer
        this.stateSpace = new TableViewer(stateTable);

        // create list-based content provider
        this.stateSpace.setContentProvider(new IStructuredContentProvider() {
            public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }

            public void dispose() { }

            public Object[] getElements(Object inputElement) {
                if ((inputElement != null) && (inputElement instanceof List)) {
                    return ((List<?>) inputElement).toArray(new Object[((List<?>) inputElement).size()]);
                }
                return null;
            }
        });

        this.stateSpace.setLabelProvider(new StateSpaceLabelProvider(this));
        getSite().setSelectionProvider(this.stateSpace);
        
        return statespaceComposite;
    }

    /**
     * Creates the coverage table (initializes the {@link coverageTimestamp} and {@link coverage} variables)  
     * @param parent
     * @param toolkit
     * @return returns the containing composite
     */
    private Composite createAndSetupCoverage(final Composite parent, final FormToolkit toolkit) {
        final Composite coverageComposite = toolkit.createComposite(parent, SWT.WRAP);
        GridLayout gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        coverageComposite.setLayout(gl);
        GridData gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        coverageComposite.setLayoutData(gd);
        
        
        final Composite headerLine = toolkit.createComposite(coverageComposite, SWT.WRAP);
        gl = new GridLayout(2, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        headerLine.setLayout(gl);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        headerLine.setLayoutData(gd);
        
        final Label title = toolkit.createLabel(headerLine, "Coverage at");
        gd = new GridData();
        gd.horizontalIndent = 0;
        gd.verticalIndent = 6;
        gd.heightHint = 22;
        gd.horizontalAlignment = SWT.BEGINNING;
        gd.verticalAlignment = SWT.BOTTOM;
        title.setLayoutData(gd);

        this.coverageTimestampText = toolkit.createText(headerLine, "", SWT.FLAT);
        this.coverageTimestampText.setEditable(false);
        gd = new GridData();
        gd.horizontalIndent = 6;
        gd.verticalIndent = 0;
        gd.minimumWidth = 150;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalAlignment = SWT.FILL;
        this.coverageTimestampText.setLayoutData(gd);
        

        final Table coverageTable
        	= toolkit.createTable(coverageComposite, SWT.MULTI | SWT.FULL_SELECTION | SWT.V_SCROLL | SWT.BORDER);
        gd = new GridData();
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = CoverageLabelProvider.MIN_WIDTH;
        gd.heightHint = 100;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalAlignment = SWT.FILL;
        coverageTable.setLayoutData(gd);

        coverageTable.setHeaderVisible(true);
        coverageTable.setLinesVisible(true);
        coverageTable.setToolTipText(TOOLTIP);

        CoverageLabelProvider.createTableColumns(coverageTable);

        // create the viewer
        this.coverage = new TableViewer(coverageTable);

        coverage.getTable().addMouseListener(new ActionClickListener(this.coverage));

        // create list-based content provider
        this.coverage.setContentProvider(new IStructuredContentProvider() {
            public void inputChanged(Viewer viewer, Object oldInput, Object newInput) { }

            public void dispose() { }

            public Object[] getElements(Object inputElement) {
                if ((inputElement != null) && (inputElement instanceof List)) {
                    return ((List<?>) inputElement).toArray(new Object[((List<?>) inputElement).size()]);
                } else if (inputElement instanceof CoverageInformation) {
                	return ((CoverageInformation) inputElement).toArray();
                }
                return null;
            }
        });

        this.coverage.setLabelProvider(new CoverageLabelProvider());
        
        getSite().setSelectionProvider(this.coverage);
        
        return coverageComposite;
    }

    /**
     * Returns the StateSpaceInformationItem objects currently being displayed in 
     * the "State space progress" area, except in temporal order--that is, in the
     * opposite order from which they are displayed.
     * 
     * @return
     */
    @SuppressWarnings("unchecked")  // generics cast
    public StateSpaceInformationItem[] getStateSpaceInformation()
    {
		List<StateSpaceInformationItem> infoList = (List<StateSpaceInformationItem>) stateSpace.getInput();
        StateSpaceInformationItem[] result = new StateSpaceInformationItem[infoList.size()];
        for (int i = 0; i < result.length; i++)
        {
            result[i] = infoList.get(result.length - i - 1);
        }
        return result;

    }

    /**
     * Provides labels for the state space table 
     */
    static class StateSpaceLabelProvider extends LabelProvider implements ITableLabelProvider, ITableFontProvider, ITableColorProvider
    {
        public final static String[] COLUMN_TITLES = new String[] { "Time", "Diameter", "States Found",
                "Distinct States", "Queue Size" };
        public final static int[] COLUMN_WIDTHS;
        public static final int MIN_WIDTH;
        public final static int COL_TIME = 0;
        public final static int COL_DIAMETER = 1;
        public final static int COL_FOUND = 2;
        public final static int COL_DISTINCT = 3;
        public final static int COL_LEFT = 4;
        
        static {
        	final double scale = 1.0;   // future functionality: UIHelper.getDisplayScaleFactor();
        	
        	COLUMN_WIDTHS = new int[5];
        	COLUMN_WIDTHS[0] = (int)(120.0 * scale);
        	COLUMN_WIDTHS[1] = (int)(60.0 * scale);
        	COLUMN_WIDTHS[2] = (int)(80.0 * scale);
        	COLUMN_WIDTHS[3] = (int)(100.0 * scale);
        	COLUMN_WIDTHS[4] = (int)(80.0 * scale);
        	
        	MIN_WIDTH = COLUMN_WIDTHS[0] + COLUMN_WIDTHS[1] + COLUMN_WIDTHS[2] + COLUMN_WIDTHS[3] + COLUMN_WIDTHS[4];
        }

        
		private boolean doHighlight = false;
		private final ResultPage resultPage;

        public StateSpaceLabelProvider(ResultPage resultPage) {
			this.resultPage = resultPage;
		}

		/* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
         */
        public Image getColumnImage(Object element, int columnIndex)
        {
            return null;
        }

		/**
         * @param stateTable
         */
        public static void createTableColumns(Table stateTable, ResultPage page)
        {
            // create table headers
            for (int i = 0; i < COLUMN_TITLES.length; i++)
            {
                TableColumn column = new TableColumn(stateTable, SWT.NULL);
                column.setWidth(COLUMN_WIDTHS[i]);
                column.setText(COLUMN_TITLES[i]);

                // The following statement attaches a listener to the column
                // header. See the ResultPageColumnListener comments.

                column.addSelectionListener(new ResultPageColumnListener(i, page));
            }
        }

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
         */
        public String getColumnText(Object element, int columnIndex)
        {
        	NumberFormat nf = NumberFormat.getIntegerInstance();
            if (element instanceof StateSpaceInformationItem)
            {
                // the "N/A" values are used for simulation mode
                StateSpaceInformationItem item = (StateSpaceInformationItem) element;
                switch (columnIndex) {
                case COL_TIME:
                    return formatInterval(resultPage.startTimestamp, item.getTime().getTime());
                case COL_DIAMETER:
                    if (item.getDiameter() >= 0)
                    {
                        return nf.format(item.getDiameter());
                    } else
                    {
                        return "--";
                    }
                case COL_FOUND:
                    return nf.format(item.getFoundStates());
                case COL_DISTINCT:
                    if (item.getDistinctStates() >= 0)
                    {
                        return nf.format(item.getDistinctStates());
                    } else
                    {
                        return "--";
                    }

                case COL_LEFT:
                    if (item.getLeftStates() >= 0)
                    {
                        return nf.format(item.getLeftStates());
                    } else
                    {
                        return "--";
                    }
                }
            }
            return null;
        }

		public Color getForeground(Object element, int columnIndex) {
			return null; // Use default color
		}

		public Color getBackground(Object element, int columnIndex) {
			final StateSpaceInformationItem ssii = (StateSpaceInformationItem) element;
			if (doHighlight && columnIndex == COL_LEFT && ssii.isMostRecent()) {
				return TLCUIActivator.getColor(SWT.COLOR_RED);
			}
			return null;
		}

		public Font getFont(Object element, int columnIndex) {
			final StateSpaceInformationItem ssii = (StateSpaceInformationItem) element;
			if (doHighlight && columnIndex == COL_LEFT && ssii.isMostRecent()) {
				return JFaceResources.getFontRegistry().getBold(JFaceResources.DEFAULT_FONT);
			}
			return null;
		}

        public void setHighlightUnexplored() {
			doHighlight  = true;
		}

		public void unsetHighlightUnexplored() {
			doHighlight = false;
		}

		private static String formatInterval(final long firstTS, final long secondTS) {
			final long interval = secondTS - firstTS;
			final long hr = TimeUnit.MILLISECONDS.toHours(interval);
			final long min = TimeUnit.MILLISECONDS.toMinutes(interval - TimeUnit.HOURS.toMillis(hr));
			final long sec = TimeUnit.MILLISECONDS
					.toSeconds(interval - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min));
			return String.format("%02d:%02d:%02d", hr, min, sec);
		}
   }

    /**
     * Provides labels for the coverage table 
     */
    static class CoverageLabelProvider extends LabelProvider implements ITableLabelProvider, ITableColorProvider
    {
        public final static String[] COLUMN_TITLES = new String[] { "Module", "Location", "Count" };
        public final static int[] COLUMN_WIDTHS;
        public static final int MIN_WIDTH;
        public final static int COL_MODULE = 0;
        public final static int COL_LOCATION = 1;
        public final static int COL_COUNT = 2;
        
        static {
        	final double scale = 1.0;	// future functionality: UIHelper.getDisplayScaleFactor();
        	
        	COLUMN_WIDTHS = new int[3];
        	COLUMN_WIDTHS[0] = (int)(80.0 * scale);
        	COLUMN_WIDTHS[1] = (int)(200.0 * scale);
        	COLUMN_WIDTHS[2] = (int)(80.0 * scale);
        	
        	MIN_WIDTH = COLUMN_WIDTHS[0] + COLUMN_WIDTHS[1] + COLUMN_WIDTHS[2];
        }
        

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnImage(java.lang.Object, int)
         */
        public Image getColumnImage(Object element, int columnIndex)
        {
            return null;
        }

        /**
         * @param stateTable
         */
        public static void createTableColumns(Table stateTable)
        {
            // create table headers
            for (int i = 0; i < COLUMN_TITLES.length; i++)
            {
                TableColumn column = new TableColumn(stateTable, SWT.NULL);
                column.setWidth(COLUMN_WIDTHS[i]);
                column.setText(COLUMN_TITLES[i]);
                column.setToolTipText(TOOLTIP);
            }
        }

        /* (non-Javadoc)
         * @see org.eclipse.jface.viewers.ITableLabelProvider#getColumnText(java.lang.Object, int)
         */
        public String getColumnText(Object element, int columnIndex)
        {
            if (element instanceof CoverageInformationItem)
            {
                CoverageInformationItem item = (CoverageInformationItem) element;
                switch (columnIndex) {
                case COL_MODULE:
                    return item.getModule();
                case COL_LOCATION:
                    return item.getLocation();
                case COL_COUNT:
                    return String.valueOf(item.getCount());
                }
            }
            return null;
        }

		public Color getForeground(Object element, int columnIndex) {
			return null; // Use default color
		}

		public Color getBackground(Object element, int columnIndex) {
			if (element instanceof CoverageInformationItem) {
				if (((CoverageInformationItem) element).getCount() == 0) {
					return TLCUIActivator.getColor(SWT.COLOR_YELLOW);
				}
			}
			return null;
		}
    }

    /**
     * A ResultPageColumnListener is a listener that handles clicks on
     * the column headers of the "State space progress" region of the
     * Result Page.  The same class is used for all the column
     * headers, with the column number indicating which column header
     * was clicked on.
     * 
     * @author lamport
     *
     */
    static class ResultPageColumnListener implements SelectionListener
    {

        private int columnNumber;
        private ResultPage resultPage;

        public ResultPageColumnListener(int columnNumber, ResultPage resultPage)
        {
            super();
            this.columnNumber = columnNumber;
            this.resultPage = resultPage;
        }

        /* (non-Javadoc)
         * @see org.eclipse.swt.events.SelectionListener#widgetDefaultSelected(org.eclipse.swt.events.SelectionEvent)
         */
        public void widgetDefaultSelected(SelectionEvent e)
        {
        	// nop
        }

        /**
         * This is called when the user clicks on the header of a column
         * of the "State space progress" region of the ResultsPage.  It 
         * raises a window with a graph of the specified column.
         */
        public void widgetSelected(SelectionEvent e)
        {
            UIHelper.runUIAsync(new DataDisplay(resultPage, columnNumber));

        }

    }

    /**
     * The run method of this class creates a shell (a window) to display
     * a graph of the appropriate State Space Progress information when the user clicks on
     * a column heading.  It then adds a PaintListener to that shell, and that 
     * listener draws the graph initially and whenever the window is resized or
     * some other event requires it to be redrawn.
     * 
     * The constructor is used to pass the arguments needed by the run method to
     * display the data.
     * 
     * Note: The location at which the shells are displayed is fixed in code
     * buried deeply.  There should probably be some thought given to where to
     * pop up the window, and perhaps a window should be popped up in the same
     * place as the last such window was popped--perhaps with a bit of random
     * variation to prevent them all from piling up.
     *  
     * @author lamport
     *
     */
    static class DataDisplay implements Runnable
    {
        int columnNumber;
        ResultPage resultPage;

        /**
         *  The constructor returns an object with null data and times arrays
         *  if there are not at least two data points.  
         *  
         * @param ssInfo
         * @param columnNumber
         */
        public DataDisplay(ResultPage resultPage, int columnNumber)
        {

            this.resultPage = resultPage;
            this.columnNumber = columnNumber;
        }

        /**
         * Much of the stuff in this run() method was copied, without much
         * understanding from Snippet245.java in the Eclipse examples.
         */
        public void run()
        {

            /*
             * The data and times arrays are set to contain the data items to be displayed
             * and the elapsed time (in milliseconds) at which each item was posted.
             * The data is obtained from the appropriate column of the ssInfo items.
             * For the Time column, the number of reports is graphed.
             */

            // The following method for getting the current display was
            // copied without understanding from someplace or other.

            String title = getGraphTitle(columnNumber, resultPage);

            // We check if a shell exists with this title, and use it if
            // it does. Otherwise, we get a new shell.
            Display display = UIHelper.getCurrentDisplay();
            boolean shellExists = false;
            Shell theShell = null;
            Shell[] shells = display.getShells();
            for (int i = 0; i < shells.length; i++)
            {
                if (shells[i].getText().equals(title))
                {
                    theShell = shells[i];
                    shellExists = true;
                    break;
                }
            }
            if (!shellExists)
            {
                theShell = new Shell(display, SWT.SHELL_TRIM);
            }
            final Shell shell = theShell;
            shell.setText(title);
            shell.setActive(); // should cause it to pop up to the top.
            if (shellExists)
            {
                shell.redraw();
                shell.update();
            } else
            {
                shell.addPaintListener(new PaintListener() {
                    public void paintControl(PaintEvent event)
                    {
                        StateSpaceInformationItem[] ssInfo = resultPage.getStateSpaceInformation();
                        if (ssInfo.length < 2)
                        {
                            return;
                        }

                        final long[] data = new long[ssInfo.length + 1];
                        long[] times = new long[ssInfo.length + 1];
                        data[0] = 0;
                        times[0] = 0;

                        long startTime = resultPage.startTimestamp;
                        TLCUIActivator.getDefault().logDebug("first reported time - starttime = "
                                + (ssInfo[0].getTime().getTime() - startTime));
                        if (startTime > ssInfo[0].getTime().getTime() - 1000)
                        {
                            startTime = ssInfo[0].getTime().getTime() - 1000;
                        }
                        for (int i = 1; i < data.length; i++)
                        {
                            switch (columnNumber) {
                            case StateSpaceLabelProvider.COL_TIME:
                                data[i] = i - 1;
                                break;
                            case StateSpaceLabelProvider.COL_DIAMETER:
                                data[i] = ssInfo[i - 1].getDiameter();
                                break;
                            case StateSpaceLabelProvider.COL_FOUND:
                                data[i] = ssInfo[i - 1].getFoundStates();
                                break;
                            case StateSpaceLabelProvider.COL_DISTINCT:
                                data[i] = ssInfo[i - 1].getDistinctStates();
                                break;
                            case StateSpaceLabelProvider.COL_LEFT:
                                data[i] = ssInfo[i - 1].getLeftStates();
                                break;
                            default:
                                return;
                            }
                            times[i] = ssInfo[i - 1].getTime().getTime() - startTime;
                        }

                        Rectangle rect = shell.getClientArea();
                        // Set maxData to the largest data value;
                        long maxData = 0;
                        for (int i = 0; i < data.length; i++)
                        {
                            if (data[i] > maxData)
                            {
                                maxData = data[i];
                            }
                        }
                        long maxTime = times[times.length - 1];

                        // event.gc.drawOval(0, 0, rect.width - 1, rect.height - 1);
                        if (maxTime > 0)
                        {
                        	// In case maxData equals 0, we use 1 instead for computing
                        	// the coordinates of the points.
                        	// (Added by LL on 6 July 2011 to fix division by zero bug.)
                        	long maxDataVal = maxData ;
                        	if (maxDataVal == 0) {
                        		maxDataVal = 1;
                        	}
                            int[] pointArray = new int[2 * data.length];
                            for (int i = 0; i < data.length; i++)
                            {
                                pointArray[2 * i] = (int) ((times[i] * rect.width) / maxTime);
                                pointArray[(2 * i) + 1] = (int) (rect.height - ((data[i] * rect.height) / maxDataVal));
                            }
                            event.gc.drawPolyline(pointArray);
                        }
                        String stringTime = "Time: ";
                        long unreportedTime = maxTime;
                        long days = maxTime / (1000 * 60 * 60 * 24);
                        if (days > 0)
                        {
                            unreportedTime = unreportedTime - days * (1000 * 60 * 60 * 24);
                            stringTime = stringTime + days + ((days == 1) ? (" day ") : (" days  "));

                        }
                        long hours = unreportedTime / (1000 * 60 * 60);
                        if (hours > 0)
                        {
                            unreportedTime = unreportedTime - hours * (1000 * 60 * 60);
                            stringTime = stringTime + hours + ((hours == 1) ? (" hour ") : (" hours  "));
                        }
                        unreportedTime = (unreportedTime + (1000 * 26)) / (1000 * 60);
                        stringTime = stringTime + unreportedTime
                                + ((unreportedTime == 1) ? (" minute ") : (" minutes  "));
                        event.gc.drawString(stringTime, 0, 0);
                        event.gc.drawString("Current: " + data[data.length - 1], 0, 15);
                        if (maxData != data[data.length - 1])
                        {
                            event.gc.drawString("Maximum: " + maxData, 0, 30);
                        }
                    }
                });
            }
            ;
            if (!shellExists)
            {
                shell.setBounds(100 + 30 * columnNumber, 100 + 30 * columnNumber, 400, 300);
            }
            shell.open();
            // The following code from the Eclipse example was eliminated.
            // It seems to cause the shell to survive after the Toolbox is
            // killed.
            //
            // while (!shell.isDisposed()) {
            // if (!display.readAndDispatch()) display.sleep();
            // }

        }

    }

    /**
     * The title of a graph consists of two parts:  the prefix, which
     * identifies the column, and the suffix, which identifies the model.
     * When we dispose of the ResultPage, we must dispose of all graph
     * window (shells) for that model.
     * 
     * @param resultPage
     * @return
     */
    private static String getGraphTitleSuffix(ResultPage resultPage)
    {
        return "(" + resultPage.getModel().getName() + ")";
    }

    private static String getGraphTitle(int columnNumber, ResultPage resultPage)
    {
        String title = StateSpaceLabelProvider.COLUMN_TITLES[columnNumber];
        if (columnNumber == StateSpaceLabelProvider.COL_TIME)
        {
            title = "Number of Progress Reports";
        }
        return title + " " + getGraphTitleSuffix(resultPage);
    }

	public Set<Section> getSections(String ...sectionIDs) {
		final Set<String> set = new HashSet<String>(Arrays.asList(sectionIDs));
		return this.sections.entrySet().stream().filter(e -> set.contains(e.getKey())).map(Map.Entry::getValue)
				.collect(Collectors.toSet());
	}
}
