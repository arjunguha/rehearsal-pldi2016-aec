using System.Net.Mail;
using $rootnamespace$.Models;

namespace $rootnamespace$.Mailers
{
    public partial class Mailer
    {
		public virtual MailMessage ForgotPassword(ForgotPasswordResetModel model)
        {
            var mailMessage = new MailMessage { Subject = "We found your lost password" };

            mailMessage.To.Add(model.EmailAddress);
		    ViewBag.Data = model;
            PopulateBody(mailMessage, viewName: "ForgotPassword");

            return mailMessage;
        }
    }
}