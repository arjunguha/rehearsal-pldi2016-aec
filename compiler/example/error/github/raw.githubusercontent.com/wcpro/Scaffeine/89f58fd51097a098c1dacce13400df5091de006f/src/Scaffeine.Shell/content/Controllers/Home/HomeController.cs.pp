namespace $rootnamespace$.Controllers.Home
{
    using System.Web.Mvc;

    public partial class HomeController : Controller
    {
        partial void IndexLoaded();

        [AllowAnonymous]
        public ActionResult Index()
        {
            IndexLoaded();
            
            return this.View();
        }
    }
}
