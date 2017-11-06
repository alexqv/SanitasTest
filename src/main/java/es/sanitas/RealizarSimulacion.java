package es.sanitas;

import java.text.ParseException;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Calendar;
import java.util.Collection;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.apache.commons.collections4.IterableUtils;
import org.apache.commons.collections4.Predicate;
import org.apache.commons.lang3.ArrayUtils;
import org.apache.commons.lang3.StringUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.ObjectMapper;

import es.sanitas.bravo.ws.stubs.contratacionws.consultasoperaciones.DatosCobertura;
import es.sanitas.bravo.ws.stubs.contratacionws.consultasoperaciones.DatosContratacionPlan;
import es.sanitas.bravo.ws.stubs.contratacionws.consultasoperaciones.DatosPlanProducto;
import es.sanitas.bravo.ws.stubs.contratacionws.documentacion.Primas;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Cobertura;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.InfoContratacion;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.InfoPromociones;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.InfoTier;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Producto;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Promocion;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.ReciboProducto;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Recibos;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Simulacion;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.TarifaBeneficiario;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.TarifaDesglosada;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.TarifaProducto;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Tarificacion;
import es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.TierProducto;
import es.sanitas.soporte.BeneficiarioPolizas;
import es.sanitas.soporte.DatosAltaAsegurados;
import es.sanitas.soporte.DatosAseguradoInclusion;
import es.sanitas.soporte.ExcepcionContratacion;
import es.sanitas.soporte.FrecuenciaEnum;
import es.sanitas.soporte.PrimasPorProducto;
import es.sanitas.soporte.ProductoPolizas;
import es.sanitas.soporte.PromocionAplicada;
import es.sanitas.soporte.RESTResponse;
import es.sanitas.soporte.SimulacionWS;
import es.sanitas.soporte.StaticVarsContratacion;
import es.sanitas.soporte.TarificacionPoliza;
import es.sanitas.soporte.TipoPromocionEnum;
import wscontratacion.beneficiario.vo.ProductoCobertura;
import wscontratacion.contratacion.fuentes.parametros.DatosAlta;
import wscontratacion.contratacion.fuentes.parametros.DatosAsegurado;
import wscontratacion.contratacion.fuentes.parametros.DatosDomicilio;
import wscontratacion.contratacion.fuentes.parametros.DatosProductoAlta;


public class RealizarSimulacion {
	
    private static final Logger LOG = LoggerFactory.getLogger( RealizarSimulacion.class );

    private static final String LINE_BREAK = "<br/>";
    private static final String DATE_FORMAT = "dd/MM/yyyy";

    private static final int NUMERO_HILOS = 4;
    private static final int TIMEOUT = 30;

    private static final List<String> TIER_PRODUCTS_LIST = Arrays.asList( "producto-1", "producto-5", "producto-3" );
    private static final String SEPARADOR_TIER = "#";
    
    
    private final ExecutorService pool = Executors.newFixedThreadPool( NUMERO_HILOS );

    private final SimpleDateFormat sdf = new SimpleDateFormat( "dd/MM/yyyy" );

    
    private SimulacionWS servicioSimulacion;
    
    private DatosContratacionPlan oDatosPlan;
    private List< String > lExcepciones;

    private List< List< PrimasPorProducto > > primasDesglosadas;
    private List< Primas > primas;
    
    private Double[] descuentosTotales;
    private Double[] pagoTotal;
    private Double[] precioConPromocion;
    
    private List< List< PromocionAplicada > > promociones;
    private List< List< es.sanitas.soporte.Recibo > > recibos;

    /**
     * Método que realiza las llamadas a las diferentes clases de simulación, para tarificar
     *
     * @param oDatosAlta
     *            Objeto del tipo DatosAlta
     * @param lProductos
     *            Listado de productos que sólo se tendrán en cuenta en caso de inclusión de
     *            productos, en el resto de casos no aplica
     * @return Map con diferentes valores obtenidos de la simulación, incluida la lista de precios
     *         por asegurado
     * @throws Exception
     *             Excepción lanzada en caso de que haya errores
     * @throws ExcepcionContratacion
     *             Excepción controlada
     */
    public Map< String, Object > realizarSimulacion( final DatosAlta oDatosAlta,
						     final List< ProductoPolizas > lProductos, 
						     final List< BeneficiarioPolizas > lBeneficiarios,
						     final boolean desglosar, 
						     final Map< String, Object > hmValores ) throws Exception, ExcepcionContratacion {
    	inicializarObjetosDeCalculo(hmValores);

        Set<FrecuenciaEnum> frecuenciasTarificar = calcularFrecuenciasTarificar(oDatosAlta, lBeneficiarios, hmValores);

        final TarificacionPoliza retornoPoliza = calcularRetornoPoliza(oDatosAlta, lProductos, lBeneficiarios, hmValores, frecuenciasTarificar);

        List< String > errores = ejecutarSimulacion(oDatosAlta, frecuenciasTarificar, retornoPoliza);

        return generarResultadosSimulacion(desglosar, errores);
    }

    @SuppressWarnings("unchecked")
	private void inicializarObjetosDeCalculo(final Map< String, Object > hmValores) {
	    oDatosPlan = ( DatosContratacionPlan ) hmValores.get( StaticVarsContratacion.DATOS_PLAN );
		lExcepciones = ( List< String > ) hmValores.get( "EXCEPCIONES" );
	
	    primasDesglosadas = new ArrayList< List< PrimasPorProducto > >();
	    primas = new ArrayList< Primas >();
	    
	    descuentosTotales = new Double[] { 0.0, 0.0, 0.0, 0.0 };
	    pagoTotal = new Double[] { 0.0, 0.0, 0.0, 0.0 };
	    precioConPromocion = new Double[] { 0.0, 0.0, 0.0, 0.0 };
	    
	    promociones = new ArrayList< List< PromocionAplicada > >();
	    recibos = new ArrayList< List< es.sanitas.soporte.Recibo > >();
    }

	private Set<FrecuenciaEnum> calcularFrecuenciasTarificar(final DatosAlta oDatosAlta,
															 final List<BeneficiarioPolizas> lBeneficiarios, 
															 final Map<String, Object> hmValores) {
		Set< FrecuenciaEnum > frecuenciasTarificar = EnumSet.noneOf( FrecuenciaEnum.class );
		
        if( lBeneficiarios != null ) {
            frecuenciasTarificar.add( FrecuenciaEnum.obtenerFrecuencia( oDatosAlta.getGenFrecuenciaPago() ) );
        } else {
        	 if( hmValores.containsKey( StaticVarsContratacion.FREC_MENSUAL ) ) {
                 frecuenciasTarificar.add( FrecuenciaEnum.MENSUAL );
             } else {
                 frecuenciasTarificar = EnumSet.allOf( FrecuenciaEnum.class );
             }
        }
        
		return frecuenciasTarificar;
	}

	private TarificacionPoliza calcularRetornoPoliza(final DatosAlta oDatosAlta,
													 final List<ProductoPolizas> lProductos, 
													 final List<BeneficiarioPolizas> lBeneficiarios,
													 final Map<String, Object> hmValores, 
													 Set<FrecuenciaEnum> frecuenciasTarificar) throws ExcepcionContratacion {
		
        Collection<Callable<TarificacionPoliza>> solvers = calcularSolvers(oDatosAlta, lProductos, lBeneficiarios, hmValores, frecuenciasTarificar);
        final List<TarificacionPoliza> resultadoSimulaciones = calcularResultadoSimulaciones(solvers);

		Predicate< TarificacionPoliza > evaluarTarificacionPolizaPredicate = new Predicate< TarificacionPoliza >() {
            public boolean evaluate( final TarificacionPoliza object ) {
                return object != null && object.getTarificacion() != null;
            }
        };
        
		final TarificacionPoliza retornoPoliza = IterableUtils.find( resultadoSimulaciones, evaluarTarificacionPolizaPredicate );

		if( retornoPoliza == null ) {
		    throw new ExcepcionContratacion( "No se ha podido obtener un precio para el presupuesto. Por favor, inténtelo de nuevo más tarde." );
		}
		
		return retornoPoliza;
	}

	private Collection<Callable<TarificacionPoliza>> calcularSolvers(final DatosAlta oDatosAlta,
																	 final List<ProductoPolizas> lProductos, 
																	 final List<BeneficiarioPolizas> lBeneficiarios,
																	 final Map<String, Object> hmValores, 
																	 Set<FrecuenciaEnum> frecuenciasTarificar) {
		
		Collection< Callable< TarificacionPoliza > > solvers = new ArrayList< Callable< TarificacionPoliza > >();
        
        for( final FrecuenciaEnum frecuencia : frecuenciasTarificar ) {
            solvers.add( simularPolizaFrecuencia( hmValores, oDatosAlta, lProductos, lBeneficiarios,  frecuencia ) );
        }
        
		return solvers;
	}

    private Callable< TarificacionPoliza > simularPolizaFrecuencia(final Map< String, Object > hmValores, 
																   final DatosAlta oDatosAlta,
																   final List< ProductoPolizas > lProductos,
																   final List< BeneficiarioPolizas > lBeneficiarios, 
																   final FrecuenciaEnum frecuencia ) {
        return new Callable< TarificacionPoliza >() {

            public TarificacionPoliza call() throws ExcepcionContratacion {
                return simular( hmValores, oDatosAlta, lProductos, lBeneficiarios, frecuencia );
            }
        };
    }

    private TarificacionPoliza simular(final Map< String, Object > hmValores, 
									   final DatosAlta oDatosAlta,
									   final List< ProductoPolizas > lProductos, 
									   final List< BeneficiarioPolizas > lBeneficiarios,
								   	   final FrecuenciaEnum frecuencia ) throws ExcepcionContratacion {
        Simulacion simulacion = generarSimulacion(hmValores, oDatosAlta, lProductos, lBeneficiarios, frecuencia);

        final RESTResponse< Tarificacion, es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Error > resultadoSimulacion = servicioSimulacion.simular( simulacion );
        
        TarificacionPoliza tarificacionPoliza = new TarificacionPoliza();
        
        if( comprobarTarificacionCorrecta(resultadoSimulacion) ) {
            tarificacionPoliza.setTarificacion( resultadoSimulacion.out );
        } else if( comprobarCodigoPromocionalInvalido(resultadoSimulacion) ) {
            tarificacionPoliza = repetirSimulacionSinCodigoPromocional(hmValores, oDatosAlta, lProductos, lBeneficiarios, frecuencia, simulacion, resultadoSimulacion);
        } else {
            System.err.println( generarMensajeLog (simulacion, resultadoSimulacion.rawResponse ) );
            throw new ExcepcionContratacion( resultadoSimulacion.error.getDescripcion() );
        }

        return tarificacionPoliza;
    }

	private Simulacion generarSimulacion(final Map<String, Object> hmValores, 
										 final DatosAlta oDatosAlta,
										 final List<ProductoPolizas> lProductos, 
										 final List<BeneficiarioPolizas> lBeneficiarios,
										 final FrecuenciaEnum frecuencia) {
		Simulacion simulacion = new Simulacion();
        
        simulacion.setOperacion( obtenerOperacion(lBeneficiarios) );
        simulacion.setInfoPromociones( obtenerInfoPromociones( oDatosAlta ) );
        simulacion.setInfoTier( obtenerTier( oDatosAlta ) );
        simulacion.setListaBeneficiarios(obtenerBeneficiarios( oDatosAlta, lProductos, lBeneficiarios, ( DatosContratacionPlan )hmValores.get( StaticVarsContratacion.DATOS_PLAN ) ) );
        simulacion.setInfoContratacion(obtenerInfoContratacion( oDatosAlta, lBeneficiarios, lProductos, frecuencia, simulacion.getOperacion()) );
        
		return simulacion;
	}

	private int obtenerOperacion(final List<BeneficiarioPolizas> lBeneficiarios) {
		return lBeneficiarios == null ? StaticVarsContratacion.ALTA_POLIZA : StaticVarsContratacion.INCLUSION_BENEFICIARIO;
	}
	
	private InfoPromociones obtenerInfoPromociones( final DatosAlta oDatosAlta ) {
        if( !(oDatosAlta instanceof DatosAltaAsegurados) ) {
        	return null;
        }
        
        InfoPromociones infoPromociones = new InfoPromociones();
        
        infoPromociones.setAutomaticas( StaticVarsContratacion.SIMULACION_PROMOCIONES_AUTOMATICAS );
        infoPromociones.setListaPromociones( recuperarPromociones(oDatosAlta) );
        
        return infoPromociones;
    }

	private Promocion[] recuperarPromociones(final DatosAlta oDatosAlta) {
        Promocion[] promociones;
        
        final String codigoPromocion = ((DatosAltaAsegurados) oDatosAlta).getCodigoPromocional();
        
        if( codigoPromocion == null ) {
        	promociones = new Promocion[ 0 ]; // Si no se ha introducido un código promocional se debe enviar de cero elementos
        } else {
            final Promocion promocion = new Promocion();
            promocion.setIdPromocion( codigoPromocion );
            
            promociones = new Promocion[ 1 ];
            promociones[ 0 ] = promocion;
        }
        
		return promociones;
	}

    private InfoTier obtenerTier( final DatosAlta oDatosAlta ) {
        if( !(oDatosAlta instanceof DatosAltaAsegurados) ) {
        	return null;
        }
        
        final String coeficientesTier = ((DatosAltaAsegurados) oDatosAlta).getCoeficientesTier();

        if( StringUtils.isEmpty( coeficientesTier ) ) {
        	return null;
        }

        InfoTier infoTier = new InfoTier();
        
        final String[] st = coeficientesTier.split( SEPARADOR_TIER );
        
        infoTier.setListaTierProductos( obtenerTierProductos(st) );
        infoTier.setTierGlobal( obtenerTierGlobal(st) );
        
        return infoTier;
    }

	private TierProducto[] obtenerTierProductos(String[] st) {
		final List< TierProducto > tierProductos = new ArrayList< TierProducto >();
		
        int i = 1;
        
        for( final String idProducto : TIER_PRODUCTS_LIST ) {
            tierProductos.add( generarTierProducto(idProducto, st, i++) );
        }
        
		return tierProductos.toArray( new TierProducto[ 0 ] );
	}

	private TierProducto generarTierProducto(String idProducto, String[] st, int indice) {
		final TierProducto tier = new TierProducto();
		
        tier.setIdProducto( Integer.valueOf( idProducto ) );
        tier.setValor( Double.valueOf( st[ indice ] ) );
        
		return tier;
	}

	private int obtenerTierGlobal(final String[] st) {
		return Double.valueOf( st[ st.length - 1 ] ).intValue();
	}

    protected es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario[] obtenerBeneficiarios(
        final DatosAlta oDatosAlta, final List< ProductoPolizas > lProductos,
        final List< BeneficiarioPolizas > lBeneficiarios, final DatosContratacionPlan oDatosPlan ) {
        final List< es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario > beneficiarios = new ArrayList< es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario >();

        // Si hay lista de beneficiarios se trata de una inclusion de beneficiarios
        if( lBeneficiarios != null && lBeneficiarios.size() > 0 ) {
            for( final BeneficiarioPolizas oBeneficiario : lBeneficiarios ) {
                final es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario beneficiario = new es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario();
                beneficiario.setFechaNacimiento(
                        cambiarFecha( oBeneficiario.getDatosPersonales().getFNacimiento(),
                                oDatosAlta.getFAlta() ) );
                beneficiario.setParentesco( 11 );
                beneficiario.setSexo( oBeneficiario.getDatosPersonales().getGenSexo() );
                if( oBeneficiario.getDatosPersonales().getIdProfesion() > 0 ) {
                    beneficiario
                            .setIdProfesion( oBeneficiario.getDatosPersonales().getIdProfesion() );
                } else {
                    beneficiario.setIdProfesion( 1 );
                }
                beneficiario.setNombre( oBeneficiario.getDatosPersonales().getNombre() );
                final Producto[] productos = obtenerProductosAsegurado(
                        oDatosAlta.getTitular().getProductosContratados(), oDatosPlan );
                beneficiario.setListaProductos( productos );
                /*
                 * String tarjeta = oBeneficiario.getSNumTarjetaSanitas(); if( !StringUtils.isEmpty(
                 * tarjeta ) ) { obtenerProcedencia(tarjeta, oBeneficiario.getDatosPersonales(),
                 * beneficiario); }
                 */
                beneficiarios.add( beneficiario );
            }
        } else {
            // Si no hay lista de beneficiarios se trata de un alta
            // Primero se procesa el titular
            es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario beneficiario = new es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario();

            beneficiario.setFechaNacimiento(
                    cambiarFecha( oDatosAlta.getTitular().getDatosPersonales().getFNacimiento(),
                            oDatosAlta.getFAlta() ) );
            beneficiario.setParentesco( 1 );
            // aunque se permite el genero 3 cuando no hay uno definido no podemos usarlo.
            // Así que enviamos un 2 (por temas de ginecologia tambien).
            beneficiario.setSexo( oDatosAlta.getTitular().getDatosPersonales().getGenSexo() == 0 ? 2
                    : oDatosAlta.getTitular().getDatosPersonales().getGenSexo() );
            beneficiario.setIdProfesion( 1 );
            beneficiario.setNombre(
                    String.valueOf( oDatosAlta.getTitular().getDatosPersonales().getNombre() ) );
            if( oDatosAlta.getTitular() instanceof DatosAseguradoInclusion ) {
                final DatosAseguradoInclusion dai = ( DatosAseguradoInclusion )oDatosAlta.getTitular();
                if( dai.getSIdCliente() != null && dai.getSIdCliente() > 0 ) {
                    beneficiario.setIdCliente( dai.getSIdCliente().intValue() );
                }
            }

            // Si hay lista de productos se incluyen como productos añadidos al alta
            Producto[] productos = obtenerProductosAsegurado(
                    oDatosAlta.getTitular().getProductosContratados(), oDatosPlan );
            if( lProductos != null && !lProductos.isEmpty() ) {
                productos = ArrayUtils.addAll( productos,
                        obtenerProductos( lProductos.get( 0 ).getProductos(), oDatosPlan ) );
            }
            beneficiario.setListaProductos( productos );

            /*
             * // Las procedencias pueden venir de tarjetas Sanitas List<String> tarjetas = ( (
             * DatosAltaAsegurados )oDatosAlta ).getLNumTarjAsegurados(); if (tarjetas != null &&
             * !tarjetas.isEmpty()){ String tarjeta = tarjetas.get( 0 ); obtenerProcedencia(tarjeta,
             * oDatosAlta.getTitular().getDatosPersonales(), beneficiario); }else{
             * beneficiario.setProcedencia( obtenerProcedencia(lProductos) ); }
             */
            beneficiarios.add( beneficiario );

            // Y luego se procesan el resto de asegurados
            if( oDatosAlta.getAsegurados() != null && oDatosAlta.getAsegurados().size() > 0 ) {
                final Iterator< DatosAseguradoInclusion > iteradorAsegurados = oDatosAlta.getAsegurados()
                        .iterator();
                int contadorBeneficiario = 1;
                while( iteradorAsegurados.hasNext() ) {
                    final DatosAseguradoInclusion oDatosAsegurado = iteradorAsegurados.next();

                    beneficiario = new es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario();

                    beneficiario.setFechaNacimiento(
                            cambiarFecha( oDatosAsegurado.getDatosPersonales().getFNacimiento(),
                                    oDatosAlta.getFAlta() ) );
                    beneficiario.setParentesco( 11 );
                    // Bravo son unos tocapelotas y aunque permiten el genero 3 cuando no hay uno
                    // definido no podemos usarlo.
                    // Así que enviamos un 2 (por temas de ginecologia tambien).
                    beneficiario.setSexo( oDatosAsegurado.getDatosPersonales().getGenSexo() == 0 ? 2
                            : oDatosAsegurado.getDatosPersonales().getGenSexo() );
                    beneficiario.setNombre( oDatosAsegurado.getDatosPersonales().getNombre() );
                    beneficiario.setIdProfesion( 1 );
                    if( oDatosAsegurado.getSIdCliente() != null ) {
                        beneficiario.setIdCliente( oDatosAsegurado.getSIdCliente().intValue() );
                    }

                    productos = obtenerProductosAsegurado(
                            oDatosAsegurado.getProductosContratados(), oDatosPlan );
                    if( lProductos != null && !lProductos.isEmpty() ) {
                        productos = ArrayUtils.addAll( productos,
                                obtenerProductos(
                                        lProductos.get( contadorBeneficiario ).getProductos(),
                                        oDatosPlan ) );
                    }
                    beneficiario.setListaProductos( productos );

                    /*
                     * if (tarjetas != null && tarjetas.size() > contadorBeneficiario){ String
                     * tarjeta = tarjetas.get( contadorBeneficiario ); obtenerProcedencia(tarjeta,
                     * oDatosAsegurado.getDatosPersonales(), beneficiario); }else{
                     * beneficiario.setProcedencia( obtenerProcedencia(lProductos) ); }
                     */
                    beneficiarios.add( beneficiario );
                    contadorBeneficiario++;
                }
            }
        }

        return beneficiarios.toArray(
                new es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario[ 0 ] );
    }

    protected InfoContratacion obtenerInfoContratacion(final DatosAlta oDatosAlta, 
													   final List< BeneficiarioPolizas > lBeneficiarios,
										   			   final List< ProductoPolizas > lProductos, 
										   			   final FrecuenciaEnum frecuencia, 
										   			   final Integer tipoOperacion) {
        final InfoContratacion infoContratacion = new InfoContratacion();

        infoContratacion.setCodigoPostal( String.format( "%05d", ( ( DatosDomicilio )oDatosAlta.getDomicilios().get( 0 ) ).getCodPostal() ) );
        infoContratacion.setFechaEfecto( oDatosAlta.getFAlta() );
        infoContratacion.setFrecuenciaPago( frecuencia.getValor() );

        if( comprobarInclusion(oDatosAlta) ) {
            agregarDatosComplementariosDeInclusion(oDatosAlta, tipoOperacion, infoContratacion);
        }
        
        if( oDatosAlta.getIdMediador() != null ) {
            infoContratacion.setIdMediador( oDatosAlta.getIdMediador().intValue() );
        }
        
        infoContratacion.setIdPlan( oDatosAlta.getIdPlan() );

        return infoContratacion;
    }

    /**
     * Comprueba si se trata de una inclusión (productos o beneficiarios) o un alta en un póliza colectiva
     * @param oDatosAlta
     * @return true si se trata de una inclusión (productos o beneficiarios) o un alta en un póliza colectiva, false en otro caso
     */
	private boolean comprobarInclusion(DatosAlta oDatosAlta) {
		return oDatosAlta.getIdPoliza() != null && oDatosAlta.getIdPoliza() != 0L;
	}

	private void agregarDatosComplementariosDeInclusion(final DatosAlta oDatosAlta, 
														final Integer tipoOperacion,
														final InfoContratacion infoContratacion) {
		final DatosAltaAsegurados oDatosAltaAsegurados = (DatosAltaAsegurados) oDatosAlta;

		// El número de póliza debe indicarse para inclusiones de beneficiarios
		// y todas las operaciones (altas/inclusiones de productos) de pólizas colectivas
		// No debe indicarse para inclusiones de productos particulares
		if (StaticVarsContratacion.INCLUSION_BENEFICIARIO == tipoOperacion.intValue()
	        || oDatosAltaAsegurados.getIdColectivo() > 0
	        || (oDatosAlta.getIdDepartamento() >= 0 && oDatosAlta.getIdEmpresa() != null)) {
		    infoContratacion.setIdPoliza( oDatosAlta.getIdPoliza().intValue() );
		}
		
		// El número de colectivo se debe incluir en inclusiones de beneficiarios
		if( StaticVarsContratacion.INCLUSION_BENEFICIARIO == tipoOperacion.intValue()) {
		    infoContratacion.setIdColectivo( oDatosAltaAsegurados.getIdColectivo());
		}
		
		// El número de departamento debe incluirse en operaciones con pólizas colectivas
		if (oDatosAlta.getIdDepartamento() >= 0) {
		    infoContratacion.setIdDepartamento( oDatosAlta.getIdDepartamento() );
		}

		// El número de empresa debe incluise en operaciones con pólizas colectivas
		if( oDatosAlta.getIdEmpresa() != null ) {
		    infoContratacion.setIdEmpresa( oDatosAlta.getIdEmpresa().intValue() );
		}
	}

	private boolean comprobarTarificacionCorrecta(final RESTResponse<Tarificacion, 
												  es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Error> response) {
		return !response.hasError() && response.out.getTarifas() != null;
	}

	private boolean comprobarCodigoPromocionalInvalido(final RESTResponse<Tarificacion, 
													   es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Error> response) {
		return response.hasError() && StaticVarsContratacion.SIMULACION_ERROR_COD_PROMOCIONAL.equalsIgnoreCase( response.error.getCodigo() );
	}

	private TarificacionPoliza repetirSimulacionSinCodigoPromocional(final Map<String, Object> hmValores,
																	 final DatosAlta oDatosAlta, 
																	 final List<ProductoPolizas> lProductos,
																	 final List<BeneficiarioPolizas> lBeneficiarios, 
																	 final FrecuenciaEnum frecuencia, 
																	 final Simulacion in,
																	 final RESTResponse<Tarificacion, es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Error> response)
																	 throws ExcepcionContratacion {
		TarificacionPoliza resultado;
		
		if( oDatosAlta instanceof DatosAltaAsegurados ) {
		    final DatosAltaAsegurados oDatosAltaAsegurados = ( DatosAltaAsegurados )oDatosAlta;
		    oDatosAltaAsegurados.setCodigoPromocional( null );
		}
		
		LOG.info( generarMensajeLog( in, response.rawResponse ) );

		resultado = simular( hmValores, oDatosAlta, lProductos, lBeneficiarios, frecuencia );
		resultado.setCodigoError( StaticVarsContratacion.SIMULACION_ERROR_COD_PROMOCIONAL );
		
		return resultado;
	}

    private String generarMensajeLog(final Simulacion in, 
    						 final String error ) {
        final StringBuffer sb = new StringBuffer();
        
        try {
            sb.append( error );
            sb.append( LINE_BREAK );
            sb.append( LINE_BREAK );
            sb.append( new ObjectMapper().writeValueAsString( in ) );
        } catch( final JsonProcessingException e ) {
            LOG.error( e.getMessage(), e );
        }
        
        return sb.toString();
    }

	private List<TarificacionPoliza> calcularResultadoSimulaciones(Collection<Callable<TarificacionPoliza>> solvers) throws ExcepcionContratacion {
        List< TarificacionPoliza > resultadoSimulaciones = new ArrayList< TarificacionPoliza >();

		CompletionService< TarificacionPoliza > ecs = new ExecutorCompletionService< TarificacionPoliza >( pool );
        int solverExistoso = sumbitSolvers(solvers, ecs);
        List< ExecutionException > resultadoExcepciones = new ArrayList< ExecutionException >();
        
        for( int i = 0; i < solverExistoso; ++i ) {
            try {
                final Future< TarificacionPoliza > future = ecs.poll( TIMEOUT, TimeUnit.SECONDS );
                
                if( future != null ) {
                    resultadoSimulaciones.add( future.get() );
                } else {
                    LOG.error( "La llamada asincrona al servicio de simulacion ha fallado por timeout" );
                }
            } catch( final InterruptedException e ) {
                LOG.error( "InterruptedException", e );
            } catch( final ExecutionException e ) {
                LOG.error( "ExecutionException", e );
                resultadoExcepciones.add( e );
            }
        }

        if( !resultadoExcepciones.isEmpty() ) {
            throw new ExcepcionContratacion(resultadoExcepciones.get( 0 ).getCause().getMessage() );
        }
        
		return resultadoSimulaciones;
	}

	private int sumbitSolvers(Collection<Callable<TarificacionPoliza>> solvers,
							  CompletionService<TarificacionPoliza> ecs) {
		int solverExistoso = 0;
        
        for( final Callable< TarificacionPoliza > s : solvers ) {
            try {
                ecs.submit( s );
                solverExistoso++;
            } catch( final RuntimeException ree ) {
                LOG.error( "RejectedExecutionException con el metodo " + s.toString(), ree );
            }
        }
        
		return solverExistoso;
	}

	private List<String> ejecutarSimulacion(final DatosAlta oDatosAlta,
											Set<FrecuenciaEnum> frecuenciasTarificar, 
											final TarificacionPoliza retornoPoliza) {
        List< String > errores = new ArrayList< String >();
        
		for( final FrecuenciaEnum frecuencia : frecuenciasTarificar ) {
            final Tarificacion retorno = validarTarificacionPoliza(retornoPoliza, errores);

            int contadorBeneficiario = 0;
            double css = 0;
            
            for( final TarifaBeneficiario tarifaBeneficiario : retorno.getTarifas().getTarifaBeneficiarios() ) {
                List< PrimasPorProducto > listaProductoPorAseg = new ArrayList< PrimasPorProducto >();
                
                listaProductoPorAseg = procesarPrimas(contadorBeneficiario, listaProductoPorAseg);

                int contadorProducto = 0;
                
                for( final TarifaProducto tarifaProducto : tarifaBeneficiario.getTarifasProductos() ) {
                    if( comprobarPromocionAplica(oDatosAlta, tarifaProducto) ) {
                        css = aplicarPromocion(frecuencia, css, listaProductoPorAseg, contadorProducto, tarifaProducto);
                    }
                    
                    contadorProducto++;
                }
                
                contadorBeneficiario++;
            }

            // Promociones aplicadas a la simulación
            promociones.add( recuperarPromocionesAgrupadas( retorno.getPromociones().getListaPromocionesPoliza(), contadorBeneficiario ) );

            procesarRecibosPrimerAño(precioConPromocion, recibos, frecuencia, retorno, css);
        }
		
		return errores;
	}

	private Tarificacion validarTarificacionPoliza(final TarificacionPoliza retornoPoliza, 
												   final List<String> errores) {
		final String codigoError = retornoPoliza.getCodigoError();
		
		if( codigoError != null && !StringUtils.isEmpty( codigoError ) ) {
		    errores.add( codigoError );
		}
		
		return retornoPoliza.getTarificacion();
	}

	private List<PrimasPorProducto> procesarPrimas(int contadorBeneficiario, 
												   List<PrimasPorProducto> listaProductoPorAseg) {
		if( primas.size() <= contadorBeneficiario ) {
		    primas.add( new Primas() );
		}
		
		if( primasDesglosadas.size() > contadorBeneficiario ) {
		    listaProductoPorAseg = primasDesglosadas.get( contadorBeneficiario );
		} else {
		    primasDesglosadas.add( listaProductoPorAseg );
		}
		
		return listaProductoPorAseg;
	}

	private boolean comprobarPromocionAplica(final DatosAlta oDatosAlta,
										 	 final TarifaProducto tarifaProducto) {
		return (tarifaProducto.getIdProducto() != 389
		        || !listaContiene(lExcepciones, StaticVarsContratacion.PROMO_ECI_COLECTIVOS )
		        || hayTarjetas( oDatosAlta )) 
				&& tarifaProducto.getIdProducto() != 670
		        || !listaContiene(lExcepciones, StaticVarsContratacion.PROMO_FARMACIA )
		        || hayTarjetas( oDatosAlta );
	}

	private double aplicarPromocion(final FrecuenciaEnum frecuencia, 
									double css,
									List<PrimasPorProducto> listaProductoPorAseg, 
									int contadorProducto, 
									final TarifaProducto tarifaProducto) {
		PrimasPorProducto oPrimasProducto;
		
		if( listaProductoPorAseg.size() > contadorProducto ) {
		    oPrimasProducto = listaProductoPorAseg.get( contadorProducto );
		} else {
			oPrimasProducto = generarNuevaPrimaPorProducto( tarifaProducto );
		    listaProductoPorAseg.add( oPrimasProducto );
		}

		final Primas primaProducto = oPrimasProducto.getPrimaProducto();
		final TarifaDesglosada tarifaDesglosada = tarifaProducto.getTarifaDesglosada();
		
		css += tarifaDesglosada.getCss();// Se calcula el CSS total para poder calcular el precio con promoción

		aplicarDescuento(frecuencia, primaProducto, tarifaDesglosada);
		
		descuentosTotales[ frecuencia.getValor() - 1 ] += tarifaDesglosada.getDescuento();
		pagoTotal[ frecuencia.getValor() - 1 ] += calcularPago(tarifaDesglosada) + tarifaDesglosada.getDescuento();
		
		return css;
	}

	private PrimasPorProducto generarNuevaPrimaPorProducto(final TarifaProducto tarifaProducto) {
		PrimasPorProducto oPrimasProducto = new PrimasPorProducto();
		
		oPrimasProducto.setCodigoProducto( tarifaProducto.getIdProducto().intValue() );
		oPrimasProducto.setNombreProducto( tarifaProducto.getDescripcion() );
		
		final DatosPlanProducto producto = getDatosProducto(tarifaProducto.getIdProducto() );
		
		if( producto != null ) {
		    oPrimasProducto.setObligatorio( producto.isSwObligatorio() ? "S" : "N" );
		    oPrimasProducto.setNombreProducto( producto.getDescComercial() );
		}
		
		return oPrimasProducto;
	}

    private DatosPlanProducto getDatosProducto(final long idProducto ) {
        for( final DatosPlanProducto producto : oDatosPlan.getProductos() ) {
            if( producto.getIdProducto() == idProducto ) {
                return producto;
            }
        }
        
        return null;
    }

	private void aplicarDescuento(final FrecuenciaEnum frecuencia, 
								  final Primas primaProducto,
							  	  final TarifaDesglosada tarifaDesglosada) {
		final double descuento = tarifaDesglosada.getDescuento();
		
		switch( frecuencia.getValor() ) {
			case 1:
			    // Mensual
			    primaProducto.setPrima( "" + descuento );
			    break;
			case 2:
			    // Trimestral
			    primaProducto.setPrima( "" + descuento );
			    break;
			case 3:
			    // Semestral
			    primaProducto.setPrima( "" + descuento*2 );
			    break;
			case 4:
			    // Anual
			    primaProducto.setPrima( "" + descuento*2 );
			    break;
			}
	}
	
	/**
	 * No sumamos tarifaDesglosada.getCss() + tarifaDesglosada.getCssre() porque
	 * la Compensación del Consorcio de Seguros sólo se aplica en la primera
	 * mensualidad. Y queremos mostrar al usuario el precio de todos los meses.
	 */
	private double calcularPago(TarifaDesglosada tarifaDesglosada) {
		return tarifaDesglosada.getPrima() + tarifaDesglosada.getISPrima();
	}

	private void procesarRecibosPrimerAño(Double[] precioConPromocion, 
										  List<List<es.sanitas.soporte.Recibo>> recibos,
										  final FrecuenciaEnum frecuencia, 
										  final Tarificacion retorno, 
										  double css) {
		Recibos recibosPrimerAño = retorno.getRecibos();
		
		if( recibosPrimerAño != null ) {
		    recibos.add( toReciboList( recibosPrimerAño.getListaRecibosProductos() ) );
		    // Se calcula el precio total con promoción. Es el importe del primer recibo sin el impuesto del consorcio
		    precioConPromocion[ frecuencia.getValor() - 1 ] = recibosPrimerAño.getReciboPoliza().getRecibos()[ 0 ].getImporte() - css;
		}
	}
	
	private Map<String, Object> generarResultadosSimulacion(final boolean desglosar, 
															final List<String> errores) {
		final Map< String, Object > hmSimulacion = new HashMap< String, Object >();
        
        hmSimulacion.put( StaticVarsContratacion.PRIMAS_SIMULACION, primas );
        hmSimulacion.put( StaticVarsContratacion.PRIMAS_SIMULACION_DESGLOSE, primasDesglosadas );
        hmSimulacion.put( StaticVarsContratacion.SIMULACION_PROVINCIA, "Madrid" );
        hmSimulacion.put( StaticVarsContratacion.HAY_DESGLOSE, desglosar );
        hmSimulacion.put( StaticVarsContratacion.DESCUENTOS_TOTALES, descuentosTotales );
        hmSimulacion.put( StaticVarsContratacion.TOTAL_ASEGURADOS, primas );
        hmSimulacion.put( StaticVarsContratacion.PROMOCIONES_SIMULACION, promociones );
        hmSimulacion.put( StaticVarsContratacion.RECIBOS_SIMULACION, recibos );
        hmSimulacion.put( StaticVarsContratacion.PAGO_TOTAL, pagoTotal );
        hmSimulacion.put( StaticVarsContratacion.ERROR, errores );

        if( hayPromocionDescuento( promociones ) ) {
            hmSimulacion.put( StaticVarsContratacion.PAGO_TOTAL, precioConPromocion );
            hmSimulacion.put( StaticVarsContratacion.PRECIOS_SIN_PROMOCION_SIMULACION, pagoTotal );
        }
        
		return hmSimulacion;
	}

    /**
     * Comprueba si alguna de las promociones aplicadas en la simulación es un descuento en la
     * prima.
     *
     * @param out
     *            simulación múltiple realizada
     */
    private boolean hayPromocionDescuento( final List< List< PromocionAplicada > > promocionesAplicadas ) {
        boolean codigoAplicado = Boolean.FALSE;
        
        if( promocionesAplicadas != null ) {
            for( final List< PromocionAplicada > promociones : promocionesAplicadas ) {
                for( final PromocionAplicada promocion : promociones ) {
                    if( promocion != null && TipoPromocionEnum.DESCUENTO_PORCENTAJE.equals( promocion.getTipoPromocion() ) ) {
                        codigoAplicado = Boolean.TRUE;
                    }
                }
            }
        }
        
        return codigoAplicado;
    }

    private Producto[] obtenerProductos( final List< ProductoCobertura > productosCobertura,
            final DatosContratacionPlan oDatosPlan ) {
        final List< Producto > productos = new ArrayList< Producto >();
        if( productosCobertura != null && !productosCobertura.isEmpty() ) {
            for( final ProductoCobertura producto : productosCobertura ) {
                productos.add( obtenerProducto( producto, oDatosPlan ) );
            }
        }

        return productos.toArray( new Producto[ 0 ] );
    }

    private Producto[] obtenerProductosAsegurado( final List< DatosProductoAlta > productosCobertura,
            final DatosContratacionPlan oDatosPlan ) {
        final List< Producto > productos = new ArrayList< Producto >();
        if( productosCobertura != null && !productosCobertura.isEmpty() ) {
            for( final DatosProductoAlta producto : productosCobertura ) {
                productos.add( obtenerProducto( producto, oDatosPlan ) );
            }
        }

        return productos.toArray( new Producto[ 0 ] );
    }

    private Producto obtenerProducto( final DatosProductoAlta productoAlta,
            final DatosContratacionPlan oDatosPlan ) {
        final Producto producto = new Producto();
        final int idProducto = productoAlta.getIdProducto();
        producto.setIdProducto( idProducto );
        producto.setListaCoberturas( obtenerCoberturas( idProducto, oDatosPlan ) );
        return producto;
    }

    private Producto obtenerProducto( final ProductoCobertura productoCobertura,
            final DatosContratacionPlan oDatosPlan ) {
        final Producto producto = new Producto();
        final int idProducto = productoCobertura.getIdProducto();
        producto.setIdProducto( idProducto );
        producto.setListaCoberturas( obtenerCoberturas( idProducto, oDatosPlan ) );
        return producto;
    }

    private Cobertura[] obtenerCoberturas( final int idProducto, final DatosContratacionPlan oDatosPlan ) {
        final List< Cobertura > coberturas = new ArrayList< Cobertura >();

        final Iterator< DatosPlanProducto > iteradorProdsPlan = oDatosPlan.getProductos().iterator();
        boolean found = false;
        while( iteradorProdsPlan.hasNext() && !found ) {
            final DatosPlanProducto productoPlan = iteradorProdsPlan.next();
            if( idProducto == productoPlan.getIdProducto() ) {
                found = true;
                for( final DatosCobertura oDatosCobertura : productoPlan.getCoberturas() ) {
                    if( oDatosCobertura.isSwObligatorio()
                            && oDatosCobertura.getCapitalMinimo() != null
                            && oDatosCobertura.getCapitalMinimo() > 0 ) {
                        final Cobertura cobertura = new Cobertura();
                        cobertura
                                .setCapital( Double.valueOf( oDatosCobertura.getCapitalMinimo() ) );
                        cobertura.setIdCobertura( oDatosCobertura.getIdCobertura().intValue() );
                        coberturas.add( cobertura );
                    }
                }
            }
        }

        return coberturas.toArray( new Cobertura[ 0 ] );
    }

    /*
     * private Procedencia obtenerProcedencia( List<ProductoPolizas> lProductos ) { Procedencia
     * procedencia = null; if (lProductos != null && !lProductos.isEmpty()){ procedencia = new
     * Procedencia(); procedencia.setIdColectivo( ( ( ProductoPolizas )lProductos.get( 0 )
     * ).getIdColectivo() ); procedencia.setIdPoliza( ( ( ProductoPolizas )lProductos.get( 0 )
     * ).getIdPoliza().intValue() ); procedencia.setIdCompania( ( ( ProductoPolizas )lProductos.get(
     * 0 ) ).getIdCompania() ); } return procedencia; } private void obtenerProcedencia(String
     * tarjeta, DatosPersona datosPersonales,
     * es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Beneficiario beneficiario){
     * IRecuperarDatosTarjetaDAO oRecuperarDatosTarj = new RecuperarDatosTarjetaDAO(); try {
     * @SuppressWarnings( "unchecked" ) Map<String, Object> hmRetorno =
     * oRecuperarDatosTarj.recuperar( tarjeta ); if( hmRetorno.get( Constantes.COD_CLIENTE ) != null
     * ) { Procedencia datosProcedencia = new Procedencia(); beneficiario.setIdCliente(
     * Integer.valueOf( String.valueOf( hmRetorno.get( Constantes.COD_CLIENTE ) ) ) ); PolizaBasico
     * oPoliza = ( PolizaBasico )hmRetorno.get( Constantes.BEAN_POLIZA );
     * datosProcedencia.setIdColectivo( Long.valueOf( oPoliza.getNumColectivo() ).intValue() );
     * datosProcedencia.setIdPoliza( Long.valueOf( oPoliza.getNumPoliza() ).intValue() );
     * datosProcedencia.setIdCompania( Long.valueOf( oPoliza.getCompania() ).intValue() );
     * util.datos.Beneficiario benef = ( util.datos.Beneficiario )hmRetorno.get(
     * Constantes.BENEFICIARIOS ); SimpleDateFormat sdf = new SimpleDateFormat(DATE_FORMAT);
     * datosPersonales.setFNacimiento(sdf.format( benef.getFNacimiento() ) );
     * datosPersonales.setGenSexo( benef.getIdSexo() ); beneficiario.setProcedencia(
     * datosProcedencia ); } } catch( Exception e ) { LOG.warn(
     * "No se ha podido recuperar los datos de la tarjeta " + tarjeta, e ); } }
     */
    /**
     * Método que recibe una fecha en formato String. Si la fecha está en formato edad, lo
     * transforma a formato fecha.
     *
     * @param fecha
     * @return la nueva fecha
     **/
    private String cambiarFecha( String fecha, final String fechaAlta ) {
        String convertida = fecha;

        if( fecha == null || "//".equals( fecha ) ) {
            // Si viene null, le ponemos que tiene 18
            fecha = "18";
        }

        if( fecha != null && !fecha.contains( "/" ) ) {
            final int edad = Integer.valueOf( fecha );
            final Calendar dob = Calendar.getInstance();
            dob.add( Calendar.YEAR, -edad );
            dob.set( Calendar.DAY_OF_MONTH, 1 );
            final SimpleDateFormat sdf = new SimpleDateFormat( DATE_FORMAT );
            convertida = sdf.format( dob.getTime() );
        }
        return convertida;
    }

    /**
     * @param oDatosAlta
     * @return true si el titular o alguno de los asegurados tiene tarjeta de sanitas.
     */
    private boolean hayTarjetas( final DatosAlta oDatosAlta ) {
        boolean tieneTarjeta = false;
        if( oDatosAlta != null && oDatosAlta.getTitular() != null ) {
            if( "S".equals( oDatosAlta.getTitular().getSwPolizaAnterior() ) ) {
                tieneTarjeta = true;
            }
        }
        if( oDatosAlta != null && oDatosAlta.getAsegurados() != null
                && oDatosAlta.getAsegurados().size() > 0 ) {
            @SuppressWarnings( "unchecked" ) final Iterator< DatosAseguradoInclusion > iterAseg = oDatosAlta
                    .getAsegurados().iterator();
            while( iterAseg.hasNext() ) {
                final DatosAsegurado aseg = iterAseg.next();
                if( "S".equals( aseg.getSwPolizaAnterior() ) ) {
                    tieneTarjeta = true;
                }
            }
        }
        return tieneTarjeta;
    }

    /**
     * Popula una lista de objetos PromocionAplicada con la información de las promociones
     * aplicadas.
     *
     * @param promociones
     *            promociones aplicadas a la tarificación.
     * @return lista de PromocionAplicada con la información de las promociones aplicadas.
     */
    private List< PromocionAplicada > toPromocionAplicadaList( final Promocion[] promociones ) {
        final List< PromocionAplicada > promocionesParam = new ArrayList< PromocionAplicada >();

        for( final Promocion promocion : promociones ) {
            final PromocionAplicada promocionParam = toPromocionAplicada( promocion );
            if( promocionParam != null ) {
                promocionesParam.add( promocionParam );
            }
        }

        return promocionesParam;
    }

    /**
     * Recupera las promociones aplicadas a la póliza.
     *
     * @param promociones
     *            promociones aplicadas a cada asegurado.
     * @param numeroAsegurados
     *            número asegurados de la póliza
     * @return promociones aplicadas a la póliza.
     */
    private List< PromocionAplicada > recuperarPromocionesAgrupadas( final es.sanitas.seg.simulacionpoliza.services.api.simulacion.vo.Promocion[] promociones,
            final int numeroAsegurados ) {

        List< PromocionAplicada > promocionesAgrupadas = new ArrayList< PromocionAplicada >();
        if( promociones != null && promociones.length > 0 ) {
            LOG.debug( promociones.toString() );
            final int numPromociones = promociones.length / numeroAsegurados;
            promocionesAgrupadas = toPromocionAplicadaList(
                    Arrays.copyOfRange( promociones, 0, numPromociones ) );
        }
        return promocionesAgrupadas;
    }

    /**
     * Popula un objeto PromocionAplicada con la información de una promoción aplicada a la
     * simulación.
     *
     * @param promocion
     *            promoción aplicada a la simulación
     * @return objeto PromocionAplicada con los datos de la promoción aplicada a la simulación.
     */
    private PromocionAplicada toPromocionAplicada( final Promocion promocion ) {
        PromocionAplicada promocionParam = null;
        if( promocion != null ) {
            promocionParam = new PromocionAplicada();
            promocionParam.setIdPromocion( promocion.getIdPromocion() != null
                    ? Long.valueOf( promocion.getIdPromocion() ) : null );
            promocionParam.setDescripcion( promocion.getDescripcion() );
            promocionParam.setTipoPromocion(
                    TipoPromocionEnum.obtenerTipoPromocion( promocion.getTipo() ) );
        }
        return promocionParam;
    }

    /**
     * Popula una lista de Recibo con la información de los recibos de la simulación.
     *
     * @param recibos
     *            recibos del primer año de la simulación
     * @return lista de Recibo con la información de los recibos de la simulación.
     */
    private List< es.sanitas.soporte.Recibo > toReciboList( final ReciboProducto[] recibos ) {
        final List< es.sanitas.soporte.Recibo > recibosList = new LinkedList< es.sanitas.soporte.Recibo >();

        if( recibos != null ) {
            for( final ReciboProducto recibo : recibos ) {
                final es.sanitas.soporte.Recibo reciboParam = toRecibo( recibo );
                if( reciboParam != null ) {
                    recibosList.add( reciboParam );
                }
            }
        }
        return recibosList;
    }

    /**
     * Popula un objeto ReciboProviderOutParam con la simulación de un recibo.
     *
     * @param recibo
     *            datos del recibo
     * @return objeto ReciboProviderOutParam con la simulación de un recibo.
     */
    private es.sanitas.soporte.Recibo toRecibo( final ReciboProducto recibo ) {
        es.sanitas.soporte.Recibo reciboParam = null;
        if( recibo != null ) {
            reciboParam = new es.sanitas.soporte.Recibo();
            final Calendar fechaEmision = Calendar.getInstance();
            try {
                fechaEmision.setTime( sdf.parse( "25/12/2016" ) );
            } catch( final ParseException e ) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            reciboParam.setFechaEmision( fechaEmision );
            reciboParam.setImporte( recibo.getIdProducto() * 1000. );
        }
        return reciboParam;
    }

    /**
     * @return the servicioSimulacion
     */
    public SimulacionWS getServicioSimulacion() {
        return servicioSimulacion;
    }

    /**
     * @param servicioSimulacion
     *            the servicioSimulacion to set
     */
    public void setServicioSimulacion( final SimulacionWS servicioSimulacion ) {
        this.servicioSimulacion = servicioSimulacion;
    }

    /**
     * Comprueba si pertenece la excepcion a la lista.
     *
     * @param lista
     *            Lista de excepciones.
     * @param elemento
     *            Dato a comprobar.
     * @return True si pertenece false en caso contrario.
     */
    public static boolean listaContiene(List<String> lista, final String elemento ) {
        LOG.debug( "Se va a comprobar si " + elemento + " estÃ¡ en la lista " + lista );
        return elemento != null && lista != null && lista.contains(elemento);
    }
}
