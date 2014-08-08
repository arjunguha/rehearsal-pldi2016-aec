namespace $rootnamespace$.Controllers.Users
{
    using Models.Users;
    using Omu.ValueInjecter;
    using System.Web.Mvc;

    public partial class UsersController
    {
        public ActionResult Details(int id)
        {
            var user = UserService.GetById(id);

            var model = new UserViewModel();
            model.InjectFrom<UnflatLoopValueInjection>(user);

            return View(model);
        }
    }
}
