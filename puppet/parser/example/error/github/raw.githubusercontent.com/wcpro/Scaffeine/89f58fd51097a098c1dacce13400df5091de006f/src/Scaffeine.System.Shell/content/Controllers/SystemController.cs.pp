namespace $rootnamespace$.Controllers
{
    using System.Web.Mvc;

    public partial class SystemController : Controller
    {        
        // GET: /Settings/
        public ActionResult Index()
        {
            return View();
        }

        public ActionResult Module()
        {
            return View();
        }
    }
}
