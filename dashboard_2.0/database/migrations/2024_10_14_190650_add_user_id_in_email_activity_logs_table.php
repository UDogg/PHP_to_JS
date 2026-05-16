<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if(Schema::hasTable('email_activity_logs'))
        {
            Schema::table('email_activity_logs', function (Blueprint $table) {
                $table->integer('user_id')->nullable();
            });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::table('email_activity_logs', function (Blueprint $table) {
            //
        });
    }
};
